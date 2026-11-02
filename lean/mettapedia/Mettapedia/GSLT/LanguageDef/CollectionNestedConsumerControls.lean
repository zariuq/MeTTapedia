import Mettapedia.OSLF.MeTTaIL.ReferenceStepEquations
import Mettapedia.OSLF.Framework.GeneralReferenceAgreement
import Mettapedia.OSLF.MeTTaIL.GeneralExecutionTotalAdmission
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledReadout
import Mettapedia.Languages.ProcessCalculi.OrientedRho.Module
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledCoverage
import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef
import Mettapedia.OSLF.MeTTaIL.ReferenceStep
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceContinuation
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionTraceAccounting
import Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution
import Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineComparison
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralRuleReceiptSource
import Mettapedia.OSLF.MeTTaIL.CanonicalMatching
import Mettapedia.OSLF.MeTTaIL.CanonicalFiring
import Mettapedia.GSLT.LanguageDef.EquationInvariant
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseNullaryTransport
import Mettapedia.GSLT.LanguageDef.WellSortedFillInversion

/-!
# Authored nested workflow and retained guard controls

The actual module rule matches a bag inside a workflow. Jobs include the
workflow occurrence under its workspace container. Each physical token
allocation starts its own retained premise continuation.
-/

open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
#module_file "../../../../../metta/gslt/module/CollectionNestedGuardedPetri.module"

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching CanonicalBags
open WellSorted CollectionOccurrenceHandoff RecursiveCollectionHandoff

def authored : LanguageDef :=
  CollectionNestedGuardedPetri.language.toOption.getD (LanguageDef.empty "")

def language : LanguageDef :=
  (authored.toCore.toOption.map (·.language)).getD (LanguageDef.empty "")

#guard CollectionNestedGuardedPetri.language.isOk
#guard authored.toCore.isOk
#guard language.rewrites.length == 1
#guard language.rewrites[0]?.map (·.premises) == some [.relationQuery "permit" []]

/-- A premise may read an already captured collection; an undeclared query
variable cannot gain a binding merely by appearing in a query. -/
def queried (metavariable : String) : LanguageDef :=
  { authored with «rewrites» := authored.rewrites.map fun rule =>
    { rule with premises := [.relationQuery "inspect" [.fvar metavariable]] } }

#guard (queried "rest").toCore.isOk
#guard !(queried "missing").toCore.isOk
#guard ((queried "rest").toCore.toOption.bind fun core => core.language.rewrites[0]?).map
  (·.premises) == some [.relationQuery "inspect" [.fvar "rest"]]

def token (label : String) : Pattern := .apply label []
def marking (items : List Pattern) : Pattern := .collection .hashBag items none
def workflow (items : List Pattern) : Pattern := .apply "Flow" [marking items]
def boxed (items : List Pattern) : Pattern := .apply "Box" [workflow items]

def source : Pattern := boxed [token "A", token "A", token "B"]
def expected : Pattern := canon (boxed [token "A", token "B", token "B"])

def plan (permitted : Bool) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile
    { language, freeTypes := [], provider :=
      { signatures := [{ relation := "permit", argumentTypes := [], modes := [] }],
        rows := if permitted then [{ relation := "permit", values := [] }] else [] } }
    { sites := .all, includeDerivedEquations := false }

structure Retained where
  job : Job
  request : RecursiveCollectionContinuation.Request

/-- This bounded control driver prepares actual published matcher answers.
Its budget does not establish whole-source completeness. -/
def prepared (permitted : Bool) (source : Pattern) (bound : List TypeExpr := []) : List Retained :=
  (jobs (plan permitted) bound (.base "Workspace") source).attach.flatMap fun selected =>
    let job := selected.val
    let valid := (jobs_exact _ _ _ _ _).mp selected.property
    let matched := RecursiveCollectionMachine.run job.request 100
      (RecursiveCollectionMachine.start job.request)
    matched.answers.attach.flatMap fun published =>
      match made : prepare job.request published.val with
      | none => []
      | some ordinary =>
        let matching := prepare_valid job.request published.val
          (RecursiveCollectionMachine.published_trace_valid job.request 100 published.property) made
        match CollectionOccurrenceContinuation.request? (plan permitted) bound (.base "Workspace") source
            job valid published.val ordinary matching 0 with
        | none => []
        | some request => [⟨job, request⟩]

def outcomes (retained : Retained) (work : Nat) : List Complete.DeepRoot.Firing :=
  RecursiveCollectionContinuation.publication retained.request
    (RecursiveCollectionContinuation.run retained.request work
      (RecursiveCollectionContinuation.start retained.request))

def receipts (permitted : Bool) (source : Pattern) (work : Nat) (bound : List TypeExpr := []) :
    List GeneralRuleJobs.Receipt :=
  (prepared permitted source bound).flatMap fun retained =>
    (outcomes retained work).filterMap fun firing =>
      CollectionOccurrenceContinuation.finish? (plan permitted) bound (.base "Workspace")
        retained.job retained.request.prepared firing

def checkControls : IO Unit := do
  for permitted in [true, false] do
    let retained := prepared permitted source
    unless retained.length == 2 do
      throw (IO.userError "Nested workflow lost a physical token allocation")
    unless (retained.map (·.request.prepared.history)).eraseDups.length == 2 do
      throw (IO.userError "Nested workflow conflated allocation histories")
    let completed := receipts permitted source 80
    unless completed.length == (if permitted then 2 else 0) do
      throw (IO.userError "Nested workflow guard produced the wrong receipt count")
    unless completed.all (fun receipt => canon receipt.target == expected) do
      throw (IO.userError "Nested workflow changed an outer context or token multiplicity")
    for frame in retained do
      let request := frame.request
      let initial := RecursiveCollectionContinuation.start request
      unless initial.answers.isEmpty do
        throw (IO.userError "A raw nested match published before its guard ran")
      let uninterrupted := RecursiveCollectionContinuation.run request 80 initial
      let interrupted := RecursiveCollectionContinuation.run request 47
        (RecursiveCollectionContinuation.run request 33 initial)
      unless RecursiveCollectionContinuation.publication request uninterrupted ==
          RecursiveCollectionContinuation.publication request interrupted do
        throw (IO.userError "Resuming a nested guard lost or repeated a publication")
      unless uninterrupted.agenda.isEmpty && uninterrupted.unresolved.isEmpty do
        throw (IO.userError "Nested workflow retained unresolved work")
  unless (prepared true (boxed [token "B"])).isEmpty do
    throw (IO.userError "A missing token generated a nested match")
  let ambient := boxed [token "A", .bvar 0, token "A", token "B"]
  let ambientTarget := canon (boxed [token "B", .bvar 0, token "A", token "B"])
  let underBinder := receipts true ambient 80 [.base "Place"]
  unless underBinder.length == 2 &&
      underBinder.all (fun receipt => canon receipt.target == ambientTarget) do
    throw (IO.userError "Nested execution lost the ambient binder context")
  IO.println "NestedCollectionContinuationControls: guard, multiplicity, outer context and resumption passed"

#eval checkControls

end Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls

/-! The guarded workflow root agrees with the independent typed rule
instance, retaining the captured assignment, completed assignment and target. -/
namespace Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.RootAgreement

set_option maxHeartbeats 1600000


open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

abbrev environment (permitted : Bool) : GeneralPremise.Environment :=
  GeneralPlanEnvironment.environment (CollectionNestedConsumerControls.plan permitted)

def rule : RewriteRule :=
  (environment true).language.rewrites[0]'(by cbv)

def specification : RuleBindingSpec :=
  ((environment true).specifications[0]'(by cbv)).2

def relations (permitted : Bool) : Engine.RelationEnv where
  tuples := fun relation _ =>
    (((environment permitted).provider.rows.filter (fun row => row.relation == relation)).map (·.values))

def context : GeneralPremise.Context := ⟨0, rule, specification, [], 0, 0⟩

theorem selected_rule (permitted : Bool) :
    (environment permitted).language.rewrites[0]? = some rule := by
  cases permitted <;> cbv

theorem selected_specification (permitted : Bool) :
    GeneralPremise.specification? (environment permitted) 0 = some specification := by
  cases permitted <;> cbv

theorem rule_bindings : rule.bindings = some specification := by cbv

theorem rule_premises : rule.premises = [.relationQuery "permit" []] := by cbv

theorem rule_admitted : admittedFor rule specification = true := by cbv

theorem provider_rows (permitted : Bool) :
    (environment permitted).provider.rows =
      if permitted then [⟨"permit", []⟩] else [] := by rfl

theorem provider_dynamic (permitted : Bool) :
    (environment permitted).provider.dynamicRelations = [] := by rfl

theorem permit_signature (permitted : Bool) :
    GeneralPremise.signature? (environment permitted).provider "permit" 0 =
      some ⟨"permit", [], []⟩ := by rfl

theorem ordinary_reduct (permitted : Bool) (assignment : Assignment) :
    reductWith? (ScopedReflectiveExecution.binderOperation
        (environment permitted).reflection rule) rule specification 0 assignment =
      reduct? rule specification 0 assignment := by rfl

theorem traced_permit_readout {permitted : Bool} {initial final : Assignment}
    {rowIndex : Nat} {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : GeneralPremise.TracedQuery (environment permitted) context
      "permit" [] initial rowIndex final origins) :
    permitted = true ∧ rowIndex = 0 ∧ final = initial ∧ origins = [] := by
  cases held with
  | row provided signature typed arguments finalTyped =>
      have sig := Option.some.inj ((permit_signature permitted).symm.trans signature)
      cases sig
      cases permitted with
      | false => simp [provider_rows] at provided
      | true =>
          cases rowIndex with
          | zero =>
              simp only [provider_rows, ↓reduceIte, List.getElem?_cons_zero,
                Option.some.injEq] at provided
              cases provided
              cases arguments
              exact ⟨rfl, rfl, rfl, rfl⟩
          | succ n => simp [provider_rows] at provided
  | dynamicRow dynamic => simp [provider_dynamic] at dynamic

theorem traced_permit {permitted : Bool} {initial : Assignment}
    (enabled : permitted = true)
    (typed : GeneralPremise.TypedAssignment (environment permitted) context initial) :
    GeneralPremise.TracedQuery (environment permitted) context
      "permit" [] initial 0 initial [] := by
  subst permitted
  exact .row rfl (permit_signature true) ⟨rfl, .nil⟩ .nil typed

theorem premises_permit_readout {permitted : Bool} {initial final : Assignment}
    {history : List GeneralPremise.Event}
    (held : GeneralPremise.PremisesHold (environment permitted) context
      rule.premises initial final history) :
    permitted = true ∧ final = initial ∧ history = [.query 0 0 0 []] := by
  rw [rule_premises] at held
  cases held with
  | cons head tail =>
      cases tail
      cases head with
      | query query =>
          obtain ⟨enabled, rowIndex, same, origins⟩ := traced_permit_readout query
          cases rowIndex
          cases same
          cases origins
          exact ⟨enabled, rfl, rfl⟩

theorem premises_permit {permitted : Bool} {initial : Assignment}
    (enabled : permitted = true)
    (typed : GeneralPremise.TypedAssignment (environment permitted) context initial) :
    GeneralPremise.PremisesHold (environment permitted) context rule.premises
      initial initial [.query 0 0 0 []] := by
  rw [rule_premises]
  exact .cons (.query (traced_permit enabled typed)) .nil

theorem permit_alternatives (permitted : Bool) :
    ConditionalEquationExecution.queryAlternatives (relations permitted)
      (environment permitted).language [] "permit" [] =
      if permitted then [⟨0, 0, []⟩] else [] := by
  cases permitted <;> cbv

theorem conditional_permit_readout {permitted : Bool} {initial final : Assignment}
    {resultIndex : Nat}
    (held : ConditionalEquationExecution.QuerySatisfiedAt (relations permitted)
      (environment permitted).language specification 0 resultIndex "permit" [] initial final) :
    permitted = true ∧ resultIndex = 0 ∧ final = initial := by
  cases held with
  | selected root alternative projected position reconciled =>
      have rootEq : root = [] := Option.some.inj projected.symm
      subst root
      rw [permit_alternatives] at position
      cases permitted with
      | false => simp at position
      | true =>
          cases resultIndex with
          | zero =>
              simp only [↓reduceIte, List.getElem?_cons_zero, Option.some.injEq] at position
              cases position
              have same : initial = final := Option.some.inj reconciled
              exact ⟨rfl, rfl, same.symm⟩
          | succ n => simp at position

theorem conditional_permit {permitted : Bool} (initial : Assignment)
    (enabled : permitted = true) :
    ConditionalEquationExecution.QuerySatisfiedAt (relations permitted)
      (environment permitted).language specification 0 0 "permit" [] initial initial := by
  subst permitted
  exact .selected [] ⟨0, 0, []⟩ rfl (by rw [permit_alternatives]; rfl) rfl

theorem conditional_premises_readout {permitted : Bool} {initial final : Assignment}
    {history : List (ScopedPremiseExecution.PremiseEvent Empty)}
    (held : ConditionalEquationExecution.QueriesSatisfied (relations permitted)
      (environment permitted).language (environment permitted).free [] rule specification 0
      rule.premises initial final history) :
    permitted = true ∧ final = initial ∧ history = [.root 0 0] := by
  rw [rule_premises] at held
  cases held with
  | cons index resultIndex relation arguments rest initial completed final history query typed objects tail =>
      cases tail
      obtain ⟨enabled, indexEq, same⟩ := conditional_permit_readout query
      cases indexEq
      cases same
      exact ⟨enabled, rfl, rfl⟩

theorem conditional_premises {permitted : Bool} {initial : Assignment}
    (enabled : permitted = true)
    (typed : GeneralPremise.TypedAssignment (environment permitted) context initial) :
    ConditionalEquationExecution.QueriesSatisfied (relations permitted)
      (environment permitted).language (environment permitted).free [] rule specification 0
      rule.premises initial initial [.root 0 0] := by
  rw [rule_premises]
  exact .cons 0 0 "permit" [] [] initial initial initial []
    (conditional_permit initial enabled) typed.1 typed.2 (.nil _ _)

theorem guarded_root_to_conditional_instance {permitted : Bool}
    {items : List Pattern} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : Assignment} {history : List GeneralPremise.Event} {target : Pattern}
    (fired : GeneralPremise.RootFiring (environment permitted) [] (.base "Workflow")
      (CollectionNestedConsumerControls.workflow items) 0 trace captured completed history target) :
    ∃ receipt : ConditionalEquationExecution.Receipt,
      ConditionalEquationExecution.RuleInstance (relations permitted)
        (environment permitted).language (environment permitted).free [] (.base "Workflow")
        rule (CollectionNestedConsumerControls.workflow items) receipt ∧
      receipt.captured = captured ∧ receipt.completed = completed ∧ receipt.target = target := by
  cases fired with
  | @fire _ _ _ _ _ actualRule actualSpec _ _ _ _ declared specified admitted
      sourceTyped matching capturedTyped premises reduced targetTyped =>
      have ruleEq : actualRule = rule :=
        Option.some.inj (declared.symm.trans (selected_rule permitted))
      cases ruleEq
      have specEq : actualSpec = specification :=
        Option.some.inj (specified.symm.trans (selected_specification permitted))
      cases specEq
      obtain ⟨enabled, same, _⟩ := premises_permit_readout premises
      cases same
      have member : captured ∈ matchRuleAt rule specification 0
          (CollectionNestedConsumerControls.workflow items) :=
        GeneralScopedMatch.matchRuleAt_iff.mpr matching.matching
      obtain ⟨matchIndex, position⟩ := List.mem_iff_getElem?.mp member
      have reducedOrdinary : reduct? rule specification 0 captured = some target := by
        simpa only [List.length_nil, ordinary_reduct] using reduced
      refine ⟨⟨matchIndex, captured, captured, [.root 0 0], target⟩, ?_, rfl, rfl, rfl⟩
      exact .fire specification rule_bindings admitted sourceTyped position
        capturedTyped.1 capturedTyped.2 (conditional_premises enabled capturedTyped)
        reducedOrdinary targetTyped

theorem conditional_instance_to_guarded_root {permitted : Bool} {items : List Pattern}
    {receipt : ConditionalEquationExecution.Receipt}
    (fired : ConditionalEquationExecution.RuleInstance (relations permitted)
      (environment permitted).language (environment permitted).free [] (.base "Workflow")
      rule (CollectionNestedConsumerControls.workflow items) receipt) :
    ∃ trace history, GeneralPremise.RootFiring (environment permitted) [] (.base "Workflow")
      (CollectionNestedConsumerControls.workflow items) 0 trace receipt.captured receipt.completed
      history receipt.target := by
  rcases receipt with ⟨matchIndex, captured, completed, history, target⟩
  cases fired with
  | fire actualSpec declared admitted sourceTyped position capturedTyped capturedObjects
      premises reduced targetTyped =>
      have specEq : actualSpec = specification :=
        Option.some.inj (declared.symm.trans rule_bindings)
      cases specEq
      obtain ⟨enabled, same, _⟩ := conditional_premises_readout premises
      cases same
      obtain ⟨trace, traced⟩ := GeneralScopedMatchMachine.matches_trace
        (GeneralScopedMatch.matchRuleAt_iff.mp (List.mem_of_getElem? position))
      have typed : GeneralPremise.TypedAssignment (environment permitted) context captured :=
        ⟨capturedTyped, capturedObjects⟩
      refine ⟨trace, [.query 0 0 0 []], ?_⟩
      exact .fire (selected_rule permitted) (selected_specification permitted) admitted sourceTyped
        traced typed (premises_permit enabled typed)
        (by simpa only [List.length_nil, ordinary_reduct] using reduced) targetTyped

theorem guarded_root_iff_conditional_instance_with_captures (permitted : Bool)
    (items : List Pattern) (captured completed : Assignment) (target : Pattern) :
    (∃ trace history, GeneralPremise.RootFiring (environment permitted) [] (.base "Workflow")
      (CollectionNestedConsumerControls.workflow items) 0 trace captured completed history target) ↔
    ∃ receipt : ConditionalEquationExecution.Receipt,
      ConditionalEquationExecution.RuleInstance (relations permitted)
        (environment permitted).language (environment permitted).free [] (.base "Workflow")
        rule (CollectionNestedConsumerControls.workflow items) receipt ∧
      receipt.captured = captured ∧ receipt.completed = completed ∧ receipt.target = target := by
  constructor
  · rintro ⟨trace, history, fired⟩
    exact guarded_root_to_conditional_instance fired
  · rintro ⟨receipt, fired, capturedEq, completedEq, targetEq⟩
    obtain ⟨trace, history, root⟩ := conditional_instance_to_guarded_root fired
    rw [capturedEq, completedEq, targetEq] at root
    exact ⟨trace, history, root⟩

theorem guarded_root_iff_conditional_instance (permitted : Bool)
    (items : List Pattern) (target : Pattern) :
    (∃ trace captured completed history,
      GeneralPremise.RootFiring (environment permitted) [] (.base "Workflow")
        (CollectionNestedConsumerControls.workflow items) 0 trace captured completed history target) ↔
    ∃ receipt : ConditionalEquationExecution.Receipt,
      ConditionalEquationExecution.RuleInstance (relations permitted)
        (environment permitted).language (environment permitted).free [] (.base "Workflow")
        rule (CollectionNestedConsumerControls.workflow items) receipt ∧ receipt.target = target := by
  constructor
  · rintro ⟨trace, captured, completed, history, fired⟩
    obtain ⟨receipt, instanceEvidence, _, _, targetEq⟩ := guarded_root_to_conditional_instance fired
    exact ⟨receipt, instanceEvidence, targetEq⟩
  · rintro ⟨receipt, instanceEvidence, targetEq⟩
    obtain ⟨trace, history, fired⟩ := conditional_instance_to_guarded_root instanceEvidence
    rw [targetEq] at fired
    exact ⟨trace, receipt.captured, receipt.completed, history, fired⟩

theorem guarded_root_requires_permit {permitted : Bool} {items : List Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List GeneralPremise.Event} {target : Pattern}
    (fired : GeneralPremise.RootFiring (environment permitted) [] (.base "Workflow")
      (CollectionNestedConsumerControls.workflow items) 0 trace captured completed history target) :
    permitted = true := by
  cases fired with
  | @fire _ _ _ _ _ actualRule actualSpec _ _ _ _ declared specified admitted
      sourceTyped matching capturedTyped premises reduced targetTyped =>
      have ruleEq : actualRule = rule :=
        Option.some.inj (declared.symm.trans (selected_rule permitted))
      cases ruleEq
      have specEq : actualSpec = specification :=
        Option.some.inj (specified.symm.trans (selected_specification permitted))
      cases specEq
      exact (premises_permit_readout premises).1

theorem refused_root (items : List Pattern) (target : Pattern) :
    ¬ ∃ trace captured completed history,
      GeneralPremise.RootFiring (environment false) [] (.base "Workflow")
        (CollectionNestedConsumerControls.workflow items) 0 trace captured completed history target := by
  rintro ⟨trace, captured, completed, history, fired⟩
  have impossible := guarded_root_requires_permit fired
  cases impossible

def sampleItems : List Pattern :=
  [CollectionNestedConsumerControls.token "A", CollectionNestedConsumerControls.token "A",
    CollectionNestedConsumerControls.token "B"]

def sampleCaptured : Assignment :=
  [("rest", ⟨[], 0, CollectionNestedConsumerControls.marking
    [CollectionNestedConsumerControls.token "A", CollectionNestedConsumerControls.token "B"]⟩)]

def sampleTarget : Pattern := CollectionNestedConsumerControls.workflow
  [CollectionNestedConsumerControls.token "B", CollectionNestedConsumerControls.token "A",
    CollectionNestedConsumerControls.token "B"]

def sampleReceipt : ConditionalEquationExecution.Receipt :=
  ⟨0, sampleCaptured, sampleCaptured, [.root 0 0], sampleTarget⟩

theorem permitted_sample_source :
    ConditionalEquationExecution.RuleInstance (relations true)
      (environment true).language (environment true).free [] (.base "Workflow")
      rule (CollectionNestedConsumerControls.workflow sampleItems) sampleReceipt := by
  apply ConditionalEquationExecution.applyRuleAtOutcome_sound
    (relations true) (environment true).language (environment true).free [] (.base "Workflow")
    rule (CollectionNestedConsumerControls.workflow sampleItems) sampleReceipt
  cbv
  exact .head _

theorem permitted_sample_root :
    ∃ trace history, GeneralPremise.RootFiring (environment true) [] (.base "Workflow")
      (CollectionNestedConsumerControls.workflow sampleItems) 0 trace sampleCaptured sampleCaptured
      history sampleTarget :=
  conditional_instance_to_guarded_root permitted_sample_source

#print axioms selected_rule
#print axioms selected_specification
#print axioms rule_bindings
#print axioms rule_premises
#print axioms rule_admitted
#print axioms provider_rows
#print axioms provider_dynamic
#print axioms permit_signature
#print axioms ordinary_reduct
#print axioms traced_permit_readout
#print axioms traced_permit
#print axioms premises_permit_readout
#print axioms premises_permit
#print axioms permit_alternatives
#print axioms conditional_permit_readout
#print axioms conditional_permit
#print axioms conditional_premises_readout
#print axioms conditional_premises
#print axioms guarded_root_to_conditional_instance
#print axioms conditional_instance_to_guarded_root
#print axioms guarded_root_iff_conditional_instance_with_captures
#print axioms guarded_root_iff_conditional_instance
#print axioms guarded_root_requires_permit
#print axioms refused_root
#print axioms permitted_sample_source
#print axioms permitted_sample_root

end Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.RootAgreement

/-! The explicit workflow context preserves the independent rule witness and its origins. -/
namespace Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.BoxAgreement

set_option maxHeartbeats 1600000


open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching DerivedContexts GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.RootAgreement
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

def boxContext : OneHoleContext := .apply "Box" [] .hole []

def boxDeclaration : GrammarRule :=
  (environment true).language.terms[4]'(by cbv)

theorem box_declaration (permitted : Bool) :
    (environment permitted).language.terms[4]? = some boxDeclaration := by
  cases permitted <;> cbv

theorem box_shape :
    boxDeclaration.label = "Box" ∧ boxDeclaration.category = "Workspace" ∧
      boxDeclaration.params = [.simple "workflow" (.base "Workflow")] ∧
      boxDeclaration.bareParams = [.simple "workflow" (.base "Workflow")] := by cbv

theorem box_ordinary : ¬ UsesBareCollection boxDeclaration := by
  simp only [UsesBareCollection, box_shape.2.2.2]
  simp

theorem box_arguments {permitted : Bool} {focus : Pattern}
    (typed : HasType (environment permitted).language (environment permitted).free []
      focus (.base "Workflow")) :
    ArgumentsHaveTypes (environment permitted).language (environment permitted).free []
      [focus] boxDeclaration.params := by
  rw [box_shape.2.2.1]
  exact .cons (by trivial) rfl typed .nil

def boxData (items : List Pattern) : SiteData :=
  (SiteData.here [] (.base "Workflow") (CollectionNestedConsumerControls.workflow items)).wrapApplication
    4 "Box" [CollectionNestedConsumerControls.workflow items] 0

theorem box_licensed {permitted : Bool} {items : List Pattern}
    (sourceTyped : OpenPatternWellSorted (environment permitted).language
      (environment permitted).free [] (.base "Workflow")
      (CollectionNestedConsumerControls.workflow items)) :
    Licensed (environment permitted).language (environment permitted).free
      (CollectionNestedConsumerControls.plan permitted).permissions.sites [] (.base "Workspace")
      (CollectionNestedConsumerControls.boxed items) (boxData items) := by
  have selected := List.mk_mem_zipIdx_iff_getElem?.mpr (box_declaration permitted)
  have lifted := Licensed.application (rule := boxDeclaration) (declaration := 4) (index := 0)
    (permissions := (CollectionNestedConsumerControls.plan permitted).permissions.sites)
    (arguments := [CollectionNestedConsumerControls.workflow items])
    (parameter := .simple "workflow" (.base "Workflow"))
    (inner := SiteData.here [] (.base "Workflow") (CollectionNestedConsumerControls.workflow items))
    selected box_ordinary (box_arguments sourceTyped.1)
    (by simpa only [isObjectPatternList, Bool.and_true] using sourceTyped.2.2.1)
    rfl (by rw [box_shape.2.2.1]; rfl) rfl (Or.inl rfl)
    (.here rfl sourceTyped.2.2.1 sourceTyped.1)
  simpa only [box_shape.1, box_shape.2.1, CollectionNestedConsumerControls.boxed, boxData] using lifted

def boxSite (permitted : Bool) (items : List Pattern)
    (sourceTyped : OpenPatternWellSorted (environment permitted).language
      (environment permitted).free [] (.base "Workflow")
      (CollectionNestedConsumerControls.workflow items)) :
    TypedContextualEquationExecution.Site (environment permitted).language
      (environment permitted).free [] (.base "Workspace") [boxContext]
      (CollectionNestedConsumerControls.boxed items) where
  context := boxContext
  focus := CollectionNestedConsumerControls.workflow items
  focusBound := []
  focusType := .base "Workflow"
  permitted := .head _
  source_eq := rfl
  typed := by
    simpa [boxData, SiteData.wrapApplication, SiteData.here, boxContext] using
      (box_licensed sourceTyped).typedAt

theorem box_accepts_replacement (permitted : Bool) (items : List Pattern) (target : Pattern) :
    (boxData items).acceptsReplacementRepresentation (environment permitted).language target = true := by
  simp only [SiteData.acceptsReplacementRepresentation, boxData, SiteData.wrapApplication,
    SiteData.here, replacementRepresentations?, box_declaration, Option.bind_some, box_shape.2.2.1,
    List.getElem?_cons_zero, matchesParameterRepresentation?, Bool.and_true]

def boxedReceipt (atomic : ConditionalEquationExecution.Receipt) :
    TypedContextualEquationExecution.Receipt :=
  ⟨0, boxContext, [], .base "Workflow", 0, atomic, boxContext.fill atomic.target⟩

theorem atomic_target_open {permitted : Bool} {items : List Pattern}
    {atomic : ConditionalEquationExecution.Receipt}
    (valid : ConditionalEquationExecution.RuleInstance (relations permitted)
      (environment permitted).language (environment permitted).free [] (.base "Workflow")
      rule (CollectionNestedConsumerControls.workflow items) atomic) :
    OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Workflow") atomic.target := by
  cases valid
  assumption

theorem atomic_box_lift {permitted : Bool} {items : List Pattern}
    (sourceTyped : OpenPatternWellSorted (environment permitted).language
      (environment permitted).free [] (.base "Workflow")
      (CollectionNestedConsumerControls.workflow items))
    {atomic : ConditionalEquationExecution.Receipt}
    (valid : ConditionalEquationExecution.RuleInstance (relations permitted)
      (environment permitted).language (environment permitted).free [] (.base "Workflow")
      rule (CollectionNestedConsumerControls.workflow items) atomic) :
    ContextualAuthoredEquationExecution.ContextualInstance (relations permitted)
      (environment permitted).language (environment permitted).free [] (.base "Workspace")
      [boxContext] (CollectionNestedConsumerControls.boxed items) 0 0 rule
      (boxSite permitted items sourceTyped) (boxedReceipt atomic) := by
  have targetTyped := atomic_target_open valid
  have outerTyped := (box_licensed sourceTyped).replace_checked atomic.target
    (box_accepts_replacement permitted items atomic.target) targetTyped.1
  exact .fill rfl rfl rfl rfl rfl valid rfl outerTyped.isWellScopedAt outerTyped

theorem boxed_instance_readout {permitted : Bool} {items : List Pattern}
    {sourceTyped : OpenPatternWellSorted (environment permitted).language
      (environment permitted).free [] (.base "Workflow")
      (CollectionNestedConsumerControls.workflow items)}
    {receipt : TypedContextualEquationExecution.Receipt}
    (valid : ContextualAuthoredEquationExecution.ContextualInstance (relations permitted)
      (environment permitted).language (environment permitted).free [] (.base "Workspace")
      [boxContext] (CollectionNestedConsumerControls.boxed items) 0 0 rule
      (boxSite permitted items sourceTyped) receipt) :
    receipt.contextIndex = 0 ∧ receipt.ruleIndex = 0 ∧ receipt.context = boxContext ∧
      receipt.focusBound = [] ∧ receipt.focusType = .base "Workflow" ∧
      receipt.target = boxContext.fill receipt.atomic.target := by
  cases valid with
  | fill origin context bound type declaration atomic target scope typing =>
      exact ⟨origin, declaration, context, bound, type, target⟩

theorem boxed_instance_to_atomic {permitted : Bool} {items : List Pattern}
    {sourceTyped : OpenPatternWellSorted (environment permitted).language
      (environment permitted).free [] (.base "Workflow")
      (CollectionNestedConsumerControls.workflow items)}
    {receipt : TypedContextualEquationExecution.Receipt}
    (valid : ContextualAuthoredEquationExecution.ContextualInstance (relations permitted)
      (environment permitted).language (environment permitted).free [] (.base "Workspace")
      [boxContext] (CollectionNestedConsumerControls.boxed items) 0 0 rule
      (boxSite permitted items sourceTyped) receipt) :
    ConditionalEquationExecution.RuleInstance (relations permitted)
      (environment permitted).language (environment permitted).free [] (.base "Workflow")
      rule (CollectionNestedConsumerControls.workflow items) receipt.atomic := by
  cases valid
  assumption

theorem guarded_root_iff_box_contextual_instance_with_captures (permitted : Bool)
    (items : List Pattern)
    (sourceTyped : OpenPatternWellSorted (environment permitted).language
      (environment permitted).free [] (.base "Workflow")
      (CollectionNestedConsumerControls.workflow items))
    (captured completed : Assignment) (target : Pattern) :
    (∃ trace history, GeneralPremise.RootFiring (environment permitted) [] (.base "Workflow")
      (CollectionNestedConsumerControls.workflow items) 0 trace captured completed history target) ↔
    ∃ receipt : TypedContextualEquationExecution.Receipt,
      ContextualAuthoredEquationExecution.ContextualInstance (relations permitted)
        (environment permitted).language (environment permitted).free [] (.base "Workspace")
        [boxContext] (CollectionNestedConsumerControls.boxed items) 0 0 rule
        (boxSite permitted items sourceTyped) receipt ∧
      receipt.atomic.captured = captured ∧ receipt.atomic.completed = completed ∧
      receipt.atomic.target = target ∧ receipt.target = boxContext.fill target := by
  constructor
  · rintro ⟨trace, history, fired⟩
    obtain ⟨atomic, valid, capturedEq, completedEq, targetEq⟩ :=
      guarded_root_to_conditional_instance fired
    refine ⟨boxedReceipt atomic, atomic_box_lift sourceTyped valid,
      capturedEq, completedEq, targetEq, ?_⟩
    exact congrArg boxContext.fill targetEq
  · rintro ⟨receipt, valid, capturedEq, completedEq, targetEq, outerEq⟩
    obtain ⟨trace, history, fired⟩ := conditional_instance_to_guarded_root
      (boxed_instance_to_atomic valid)
    rw [capturedEq, completedEq, targetEq] at fired
    exact ⟨trace, history, fired⟩

theorem guarded_root_iff_box_contextual_instance (permitted : Bool) (items : List Pattern)
    (sourceTyped : OpenPatternWellSorted (environment permitted).language
      (environment permitted).free [] (.base "Workflow")
      (CollectionNestedConsumerControls.workflow items)) (target : Pattern) :
    (∃ trace captured completed history,
      GeneralPremise.RootFiring (environment permitted) [] (.base "Workflow")
        (CollectionNestedConsumerControls.workflow items) 0 trace captured completed history target) ↔
    ∃ receipt : TypedContextualEquationExecution.Receipt,
      ContextualAuthoredEquationExecution.ContextualInstance (relations permitted)
        (environment permitted).language (environment permitted).free [] (.base "Workspace")
        [boxContext] (CollectionNestedConsumerControls.boxed items) 0 0 rule
        (boxSite permitted items sourceTyped) receipt ∧
      receipt.atomic.target = target ∧ receipt.target = boxContext.fill target := by
  constructor
  · rintro ⟨trace, captured, completed, history, fired⟩
    obtain ⟨receipt, valid, _, _, targetEq, outerEq⟩ :=
      (guarded_root_iff_box_contextual_instance_with_captures permitted items sourceTyped
        captured completed target).mp ⟨trace, history, fired⟩
    exact ⟨receipt, valid, targetEq, outerEq⟩
  · rintro ⟨receipt, valid, targetEq, outerEq⟩
    obtain ⟨trace, history, fired⟩ :=
      (guarded_root_iff_box_contextual_instance_with_captures permitted items sourceTyped
        receipt.atomic.captured receipt.atomic.completed target).mpr
          ⟨receipt, valid, rfl, rfl, targetEq, outerEq⟩
    exact ⟨trace, receipt.atomic.captured, receipt.atomic.completed, history, fired⟩

theorem box_declarations (permitted : Bool) :
    (environment permitted).language.terms.filter (fun declaration => declaration.label == "Box") =
      [boxDeclaration] := by
  cases permitted <;> cbv

theorem box_declaration_unique {permitted : Bool} {declaration : GrammarRule}
    (member : declaration ∈ (environment permitted).language.terms)
    (label : declaration.label = "Box") : declaration = boxDeclaration := by
  have filtered : declaration ∈ (environment permitted).language.terms.filter
      (fun declaration => declaration.label == "Box") :=
    List.mem_filter.mpr ⟨member, by simp only [label, beq_self_eq_true]⟩
  rw [box_declarations] at filtered
  exact List.mem_singleton.mp filtered

theorem box_typedAt_indices {permitted : Bool} {focus : Pattern}
    {focusBound : List TypeExpr} {focusType : TypeExpr}
    (selected : TypedAt (environment permitted).language (environment permitted).free
      focus boxContext [] (.base "Workspace") focusBound focusType) :
    focusBound = [] ∧ focusType = .base "Workflow" := by
  change TypedAt (environment permitted).language (environment permitted).free
    focus (.apply "Box" [] .hole []) [] (.base "Workspace") focusBound focusType at selected
  generalize contextEq : (OneHoleContext.apply "Box" [] .hole []) = context at selected
  generalize ambientEq : (TypeExpr.base "Workspace") = ambientType at selected
  cases selected with
  | here _ => cases contextEq
  | @application declaration before after inner bound focusBound expected result
      beforeParams afterParams parameter member ordinary arguments shape length parameterType innerSelected =>
      have frames := OneHoleContext.apply.inj contextEq
      have declarationEq := box_declaration_unique member frames.1.symm
      cases declarationEq
      cases frames.2.1
      cases frames.2.2.1
      cases frames.2.2.2
      have beforeEmpty : beforeParams = [] := List.length_eq_zero_iff.mp length
      subst beforeParams
      rw [box_shape.2.2.1] at shape
      have parameterEq : parameter = .simple "workflow" (.base "Workflow") :=
        (List.cons.inj shape).1.symm
      cases parameterEq
      have expectedEq : expected = .base "Workflow" := Option.some.inj parameterType.symm
      simpa only [expectedEq] using innerSelected.hole_indices
  | lambda _ => cases contextEq
  | multiLambda _ => cases contextEq
  | substBody _ _ => cases contextEq
  | substReplacement _ _ => cases contextEq
  | collection _ _ => cases contextEq
  | collectionConstructor _ _ _ _ => cases contextEq

theorem box_site_fields {permitted : Bool} {items : List Pattern}
    (site : TypedContextualEquationExecution.Site (environment permitted).language
      (environment permitted).free [] (.base "Workspace") [boxContext]
      (CollectionNestedConsumerControls.boxed items)) :
    site.context = boxContext ∧ site.focus = CollectionNestedConsumerControls.workflow items ∧
      site.focusBound = [] ∧ site.focusType = .base "Workflow" := by
  have contextEq : site.context = boxContext := List.mem_singleton.mp site.permitted
  have sourceEq := site.source_eq
  rw [contextEq] at sourceEq
  change Pattern.apply "Box" [site.focus] =
    Pattern.apply "Box" [CollectionNestedConsumerControls.workflow items] at sourceEq
  have focusEq := (List.cons.inj (Pattern.apply.inj sourceEq).2).1
  have selected := site.typed
  rw [contextEq] at selected
  have focusIndices := box_typedAt_indices selected
  exact ⟨contextEq, focusEq, focusIndices⟩

theorem any_boxed_instance_to_atomic {permitted : Bool} {items : List Pattern}
    {site : TypedContextualEquationExecution.Site (environment permitted).language
      (environment permitted).free [] (.base "Workspace") [boxContext]
      (CollectionNestedConsumerControls.boxed items)}
    {receipt : TypedContextualEquationExecution.Receipt}
    (valid : ContextualAuthoredEquationExecution.ContextualInstance (relations permitted)
      (environment permitted).language (environment permitted).free [] (.base "Workspace")
      [boxContext] (CollectionNestedConsumerControls.boxed items) 0 0 rule site receipt) :
    ConditionalEquationExecution.RuleInstance (relations permitted)
      (environment permitted).language (environment permitted).free [] (.base "Workflow")
      rule (CollectionNestedConsumerControls.workflow items) receipt.atomic := by
  obtain ⟨_, focusEq, boundEq, typeEq⟩ := box_site_fields site
  cases valid with
  | fill origin context bound type declaration atomic target scope typing =>
      simpa only [ContextualAuthoredEquationExecution.conditionalEvidence, focusEq, boundEq, typeEq] using atomic

theorem any_boxed_instance_readout {permitted : Bool} {items : List Pattern}
    {site : TypedContextualEquationExecution.Site (environment permitted).language
      (environment permitted).free [] (.base "Workspace") [boxContext]
      (CollectionNestedConsumerControls.boxed items)}
    {receipt : TypedContextualEquationExecution.Receipt}
    (valid : ContextualAuthoredEquationExecution.ContextualInstance (relations permitted)
      (environment permitted).language (environment permitted).free [] (.base "Workspace")
      [boxContext] (CollectionNestedConsumerControls.boxed items) 0 0 rule site receipt) :
    receipt.contextIndex = 0 ∧ receipt.ruleIndex = 0 ∧ receipt.context = boxContext ∧
      receipt.focusBound = [] ∧ receipt.focusType = .base "Workflow" ∧
      receipt.target = boxContext.fill receipt.atomic.target := by
  obtain ⟨contextEq, _, boundEq, typeEq⟩ := box_site_fields site
  cases valid with
  | fill origin context bound type declaration atomic target scope typing =>
      exact ⟨origin, declaration, context.trans contextEq, bound.trans boundEq,
        type.trans typeEq, by simpa only [ContextualAuthoredEquationExecution.conditionalEvidence, contextEq] using target⟩

theorem atomic_source_open {permitted : Bool} {items : List Pattern}
    {atomic : ConditionalEquationExecution.Receipt}
    (valid : ConditionalEquationExecution.RuleInstance (relations permitted)
      (environment permitted).language (environment permitted).free [] (.base "Workflow")
      rule (CollectionNestedConsumerControls.workflow items) atomic) :
    OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Workflow") (CollectionNestedConsumerControls.workflow items) := by
  cases valid
  assumption

theorem guarded_root_iff_exists_box_contextual_instance_with_captures (permitted : Bool)
    (items : List Pattern) (captured completed : Assignment) (target : Pattern) :
    (∃ trace history, GeneralPremise.RootFiring (environment permitted) [] (.base "Workflow")
      (CollectionNestedConsumerControls.workflow items) 0 trace captured completed history target) ↔
    ∃ (site : TypedContextualEquationExecution.Site (environment permitted).language
        (environment permitted).free [] (.base "Workspace") [boxContext]
        (CollectionNestedConsumerControls.boxed items))
      (receipt : TypedContextualEquationExecution.Receipt),
      ContextualAuthoredEquationExecution.ContextualInstance (relations permitted)
        (environment permitted).language (environment permitted).free [] (.base "Workspace")
        [boxContext] (CollectionNestedConsumerControls.boxed items) 0 0 rule site receipt ∧
      receipt.atomic.captured = captured ∧ receipt.atomic.completed = completed ∧
      receipt.atomic.target = target ∧ receipt.target = boxContext.fill target := by
  constructor
  · rintro ⟨trace, history, fired⟩
    obtain ⟨atomic, valid, capturedEq, completedEq, targetEq⟩ :=
      guarded_root_to_conditional_instance fired
    exact ⟨boxSite permitted items (atomic_source_open valid), boxedReceipt atomic,
      atomic_box_lift (atomic_source_open valid) valid, capturedEq, completedEq, targetEq,
      congrArg boxContext.fill targetEq⟩
  · rintro ⟨site, receipt, valid, capturedEq, completedEq, targetEq, outerEq⟩
    obtain ⟨trace, history, fired⟩ := conditional_instance_to_guarded_root
      (any_boxed_instance_to_atomic valid)
    rw [capturedEq, completedEq, targetEq] at fired
    exact ⟨trace, history, fired⟩

theorem guarded_root_iff_exists_box_contextual_instance (permitted : Bool)
    (items : List Pattern) (target : Pattern) :
    (∃ trace captured completed history,
      GeneralPremise.RootFiring (environment permitted) [] (.base "Workflow")
        (CollectionNestedConsumerControls.workflow items) 0 trace captured completed history target) ↔
    ∃ (site : TypedContextualEquationExecution.Site (environment permitted).language
        (environment permitted).free [] (.base "Workspace") [boxContext]
        (CollectionNestedConsumerControls.boxed items))
      (receipt : TypedContextualEquationExecution.Receipt),
      ContextualAuthoredEquationExecution.ContextualInstance (relations permitted)
        (environment permitted).language (environment permitted).free [] (.base "Workspace")
        [boxContext] (CollectionNestedConsumerControls.boxed items) 0 0 rule site receipt ∧
      receipt.atomic.target = target ∧ receipt.target = boxContext.fill target := by
  constructor
  · rintro ⟨trace, captured, completed, history, fired⟩
    obtain ⟨site, receipt, valid, _, _, targetEq, outerEq⟩ :=
      (guarded_root_iff_exists_box_contextual_instance_with_captures permitted items
        captured completed target).mp ⟨trace, history, fired⟩
    exact ⟨site, receipt, valid, targetEq, outerEq⟩
  · rintro ⟨site, receipt, valid, targetEq, outerEq⟩
    obtain ⟨trace, history, fired⟩ :=
      (guarded_root_iff_exists_box_contextual_instance_with_captures permitted items
        receipt.atomic.captured receipt.atomic.completed target).mpr
          ⟨site, receipt, valid, rfl, rfl, targetEq, outerEq⟩
    exact ⟨trace, receipt.atomic.captured, receipt.atomic.completed, history, fired⟩

theorem permitted_sample_box :
    ∃ (site : TypedContextualEquationExecution.Site (environment true).language
        (environment true).free [] (.base "Workspace") [boxContext]
        (CollectionNestedConsumerControls.boxed sampleItems))
      (receipt : TypedContextualEquationExecution.Receipt),
      ContextualAuthoredEquationExecution.ContextualInstance (relations true)
        (environment true).language (environment true).free [] (.base "Workspace")
        [boxContext] (CollectionNestedConsumerControls.boxed sampleItems) 0 0 rule site receipt ∧
      receipt.atomic.captured = sampleCaptured ∧ receipt.atomic.completed = sampleCaptured ∧
      receipt.atomic.target = sampleTarget ∧ receipt.target = boxContext.fill sampleTarget :=
  (guarded_root_iff_exists_box_contextual_instance_with_captures true sampleItems
    sampleCaptured sampleCaptured sampleTarget).mp permitted_sample_root

theorem refused_box_instance {items : List Pattern}
    {site : TypedContextualEquationExecution.Site (environment false).language
      (environment false).free [] (.base "Workspace") [boxContext]
      (CollectionNestedConsumerControls.boxed items)}
    {receipt : TypedContextualEquationExecution.Receipt}
    (valid : ContextualAuthoredEquationExecution.ContextualInstance (relations false)
      (environment false).language (environment false).free [] (.base "Workspace")
      [boxContext] (CollectionNestedConsumerControls.boxed items) 0 0 rule site receipt) : False := by
  obtain ⟨trace, history, fired⟩ := conditional_instance_to_guarded_root
    (any_boxed_instance_to_atomic valid)
  have impossible := guarded_root_requires_permit fired
  cases impossible

#print axioms box_declaration
#print axioms box_shape
#print axioms box_ordinary
#print axioms box_arguments
#print axioms box_licensed
#print axioms box_accepts_replacement
#print axioms atomic_target_open
#print axioms atomic_box_lift
#print axioms boxed_instance_readout
#print axioms boxed_instance_to_atomic
#print axioms guarded_root_iff_box_contextual_instance_with_captures
#print axioms guarded_root_iff_box_contextual_instance
#print axioms box_declarations
#print axioms box_declaration_unique
#print axioms box_typedAt_indices
#print axioms box_site_fields
#print axioms any_boxed_instance_to_atomic
#print axioms any_boxed_instance_readout
#print axioms atomic_source_open
#print axioms guarded_root_iff_exists_box_contextual_instance_with_captures
#print axioms guarded_root_iff_exists_box_contextual_instance
#print axioms permitted_sample_box
#print axioms refused_box_instance
#print axioms boxSite

end Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.BoxAgreement

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.SearchAgreement

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching DerivedContexts GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted GeneralTypedOccurrence
open CanonicalBags GeneralPremise RootAgreement BoxAgreement

theorem rule_left : rule.left =
    .apply "Flow" [.collection .hashBag [token "A"] (some "rest")] := by cbv

private theorem atom_match_comparison
    (first second : String → Pattern → Pattern → Bool) (path : List Nat)
    (initial : Assignment) (target : Pattern) :
    matchAtWith first rule specification 0 .left path 0 initial (token "A") target =
      matchAtWith second rule specification 0 .left path 0 initial (token "A") target := by
  cases target with
  | apply label arguments =>
      simp only [token, matchAtWith]
      split
      · cases arguments <;> simp only [matchArgsAtWith]
      · rfl
  | _ => simp only [token, matchAtWith]

private theorem atom_match_initial
    (compare : String → Pattern → Pattern → Bool) (path : List Nat)
    (initial : Assignment) (target : Pattern) {found : Assignment}
    (member : found ∈ matchAtWith compare rule specification 0 .left path 0 initial
      (token "A") target) : found = initial := by
  cases target with
  | apply label arguments =>
      simp only [token, matchAtWith] at member
      split at member
      · cases arguments with
        | nil => simpa only [matchArgsAtWith, List.mem_singleton] using member
        | cons head tail => simp only [matchArgsAtWith, List.not_mem_nil] at member
      · simp only [List.not_mem_nil] at member
  | _ => simp only [token, matchAtWith, List.not_mem_nil] at member

private theorem fresh_rest_comparison
    (first second : String → Pattern → Pattern → Bool) (path : List Nat)
    (items : List Pattern) :
    captureRestWith? first rule specification 0 0 .left path [] "rest" .hashBag items =
      captureRestWith? second rule specification 0 0 .left path [] "rest" .hashBag items := by
  simp only [captureRestWith?, captureWith?, assignWith, lookup, List.find?_nil,
    Option.map_none]

private theorem bag_match_comparison
    (first second : String → Pattern → Pattern → Bool) (path : List Nat)
    (items : List Pattern) :
    matchBagAtWith first rule specification 0 .left path 0 [] 0 [token "A"] (some "rest") .hashBag items =
      matchBagAtWith second rule specification 0 .left path 0 [] 0 [token "A"] (some "rest") .hashBag items := by
  simp only [matchBagAtWith]
  apply List.flatMap_congr
  rintro ⟨target, index⟩ member
  dsimp only
  rw [atom_match_comparison first second]
  apply List.flatMap_congr
  intro found member
  have same := atom_match_initial second (path ++ [0]) [] target member
  subst found
  simp only [fresh_rest_comparison first second]

private theorem marking_match_comparison
    (first second : String → Pattern → Pattern → Bool) (path : List Nat)
    (target : Pattern) :
    matchAtWith first rule specification 0 .left path 0 []
        (.collection .hashBag [token "A"] (some "rest")) target =
      matchAtWith second rule specification 0 .left path 0 []
        (.collection .hashBag [token "A"] (some "rest")) target := by
  cases target with
  | collection kind items rest =>
      simp only [matchAtWith]
      split
      · exact bag_match_comparison first second path items
      · rfl
  | _ => simp only [token, matchAtWith]

theorem rule_match_comparison (first second : String → Pattern → Pattern → Bool)
    (target : Pattern) :
    matchAtWith first rule specification 0 .left [] 0 [] rule.left target =
      matchAtWith second rule specification 0 .left [] 0 [] rule.left target := by
  rw [rule_left]
  cases target with
  | apply label arguments =>
      simp only [matchAtWith]
      split
      · cases arguments with
        | nil => simp only [matchArgsAtWith]
        | cons head tail =>
            simp only [matchArgsAtWith]
            rw [marking_match_comparison first second]
            apply List.flatMap_congr
            intro found member
            cases tail <;> simp only [matchArgsAtWith]
      · rfl
  | _ => simp only [token, matchAtWith]

theorem guarded_match_same {source other : Pattern} {captured : Assignment}
    (matching : GeneralScopedMatch.Matches rule specification 0 .left [] 0 [] rule.left source captured)
    (same : Same source other) :
    ∃ assignment,
      GeneralScopedMatch.Matches rule specification 0 .left [] 0 [] rule.left other assignment ∧
      AssignSame captured assignment := by
  have member := matching.complete
  change captured ∈ matchAtWith literalBodyComparison rule specification 0 .left [] 0 []
    rule.left source at member
  rw [rule_match_comparison literalBodyComparison canonCompare] at member
  obtain ⟨assignment, matched, compared⟩ :=
    matchAtWith_same rule specification 0 rule.left .left [] 0 [] [] source other
      (by cbv) List.Forall₂.nil same captured member
  rw [rule_match_comparison canonCompare literalBodyComparison] at matched
  exact ⟨assignment, GeneralScopedMatch.matchAt_sound matched, compared⟩

private theorem same_assignment_entry {first second : Assignment} (same : AssignSame first second)
    {captureName : String} {value : ContextualValue} (member : (captureName, value) ∈ second) :
    ∃ prior, (captureName, prior) ∈ first ∧ ValueSame prior value := by
  induction same with
  | nil => cases member
  | @cons left right lefts rights related rest ih =>
      rcases List.mem_cons.mp member with sameHead | later
      · cases sameHead
        rcases left with ⟨leftName, leftValue⟩
        have named : leftName = captureName := related.1
        cases named
        exact ⟨leftValue, .head _, related.2⟩
      · obtain ⟨prior, priorMember, compared⟩ := ih later
        exact ⟨prior, .tail _ priorMember, compared⟩

theorem typed_assignment_same {environment : Environment} {context : Context}
    {first second : Assignment} (same : AssignSame first second)
    (typed : TypedAssignment environment context first) : TypedAssignment environment context second := by
  constructor
  · intro captureName value member
    obtain ⟨prior, priorMember, compared⟩ := same_assignment_entry same member
    obtain ⟨dependencies, expected, declared, sorted, dependencyEq, ambientEq, bodyTyped⟩ :=
      typed.1 captureName prior priorMember
    refine ⟨dependencies, expected, declared, sorted, compared.1.symm.trans dependencyEq,
      compared.2.1.symm.trans ambientEq, ?_⟩
    exact hasType_of_chain (eqvGen_reflTransGen ((same_iff _ _).mp compared.2.2)) bodyTyped
  · intro captureName value member
    obtain ⟨prior, priorMember, compared⟩ := same_assignment_entry same member
    rw [← objectPattern_of_chain (eqvGen_reflTransGen ((same_iff _ _).mp compared.2.2))]
    exact typed.2 captureName prior priorMember

/-- Ordinary firing transports across intrinsic bag equality with the same nullary premise history. -/
theorem guarded_root_same_source {permitted : Bool} {items others : List Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List Event} {target : Pattern}
    (same : Same (workflow items) (workflow others))
    (fired : RootFiring (environment permitted) [] (.base "Workflow") (workflow items) 0
      trace captured completed history target) :
    ∃ trace' assignment target',
      RootFiring (environment permitted) [] (.base "Workflow") (workflow others) 0
        trace' assignment assignment history target' ∧ Same target target' := by
  cases fired with
  | @fire _ _ _ _ _ actualRule actualSpec _ _ _ _ declared specified admitted
      sourceTyped matching capturedTyped premises reduced targetTyped =>
      have ruleEq : actualRule = rule := Option.some.inj (declared.symm.trans (selected_rule permitted))
      cases ruleEq
      have specEq : actualSpec = specification :=
        Option.some.inj (specified.symm.trans (selected_specification permitted))
      cases specEq
      have guards : NullaryGuards rule.premises := by
        rw [rule_premises]
        intro premise member
        have same := List.mem_singleton.mp member
        subst premise
        exact ⟨"permit", rfl⟩
      obtain ⟨completedEq, transport⟩ := premises.nullary_transport guards
      cases completedEq
      obtain ⟨assignment, matched, compared⟩ := guarded_match_same matching.matching same
      obtain ⟨trace', traced⟩ := GeneralScopedMatchMachine.matches_trace matched
      have typed := typed_assignment_same compared capturedTyped
      obtain ⟨target', reduced', targetSame⟩ := instantiateWith?_same rule specification 0
        (ScopedReflectiveExecution.binderOperation (environment permitted).reflection rule)
        (binderOperation_same _ rule) rule.right .right [] 0 captured assignment target compared reduced
      refine ⟨trace', assignment, target', ?_, targetSame⟩
      exact .fire (selected_rule permitted) (selected_specification permitted) admitted
        (openPatternWellSorted_of_eqvGen ((same_iff _ _).mp same) sourceTyped)
        traced typed (transport assignment typed) reduced'
        (openPatternWellSorted_of_eqvGen ((same_iff _ _).mp targetSame) targetTyped)

theorem place_declaration_shape {permitted : Bool} {declaration : GrammarRule}
    (member : declaration ∈ (environment permitted).language.terms)
    (category : declaration.category = "Place") :
    (declaration.label = "A" ∨ declaration.label = "B") ∧
      declaration.params = [] ∧ declaration.bareParams = [] := by
  have inventory : ((environment permitted).language.terms.all fun declaration =>
      decide (declaration.category = "Place" →
        (declaration.label = "A" ∨ declaration.label = "B") ∧
          declaration.params = [] ∧ declaration.bareParams = [])) = true := by
    cases permitted <;> cbv
  exact (of_decide_eq_true (List.all_eq_true.mp inventory declaration member)) category

theorem flow_declaration_shape {permitted : Bool} {declaration : GrammarRule}
    (member : declaration ∈ (environment permitted).language.terms)
    (label : declaration.label = "Flow") :
    declaration.params = [.simple "marking" (.base "Marking")] := by
  have inventory : ((environment permitted).language.terms.all fun declaration =>
      decide (declaration.label = "Flow" →
        declaration.params = [.simple "marking" (.base "Marking")])) = true := by
    cases permitted <;> cbv
  exact (of_decide_eq_true (List.all_eq_true.mp inventory declaration member)) label

theorem marking_declaration_shape {permitted : Bool} {declaration : GrammarRule}
    (member : declaration ∈ (environment permitted).language.terms)
    (category : declaration.category = "Marking") :
    declaration.bareParams = [.simple "items" (.collection .hashBag (.base "Place"))] := by
  have inventory : ((environment permitted).language.terms.all fun declaration =>
      decide (declaration.category = "Marking" →
        declaration.bareParams = [.simple "items" (.collection .hashBag (.base "Place"))])) = true := by
    cases permitted <;> cbv
  exact (of_decide_eq_true (List.all_eq_true.mp inventory declaration member)) category

theorem closed_place {permitted : Bool} {pattern : Pattern}
    (typed : HasType (environment permitted).language (environment permitted).free []
      pattern (.base "Place"))
    (object : isObjectPattern pattern = true) : pattern = token "A" ∨ pattern = token "B" := by
  cases pattern with
  | bvar index =>
      cases typed with
      | bvar selected => simp only [List.getElem?_nil] at selected; cases selected
  | fvar captureName =>
      cases typed with
      | fvar selected =>
          have empty : (environment permitted).free captureName = none := by rfl
          rw [empty] at selected
          cases selected
  | apply label arguments =>
      obtain ⟨declaration, member, labelEq, _, typeEq, argumentsTyped⟩ := hasType_apply_inversion typed
      obtain ⟨labels, parameterShape, _⟩ :=
        place_declaration_shape member (TypeExpr.base.inj typeEq).symm
      rw [parameterShape] at argumentsTyped
      cases argumentsTyped
      rcases labels with a | b
      · exact Or.inl (by rw [labelEq, a]; rfl)
      · exact Or.inr (by rw [labelEq, b]; rfl)
  | collection kind items rest =>
      rcases hasType_collection_inversion typed with ⟨type, impossible, _⟩ |
        ⟨declaration, parameter, type, member, shape, category, _⟩
      · cases impossible
      · have bare := (place_declaration_shape member (TypeExpr.base.inj category).symm).2.2
        rw [bare] at shape
        cases shape
  | «subst» body replacement => cases object
  | lambda binder body => cases typed
  | multiLambda arity binders body => cases typed

theorem workflow_open_of_boxed {permitted : Bool} {items : List Pattern}
    (typed : OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Workspace") (boxed items)) :
    OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Workflow") (workflow items) := by
  obtain ⟨declaration, member, labelEq, _, _, argumentsTyped⟩ := hasType_apply_inversion typed.1
  have declarationEq := box_declaration_unique member labelEq.symm
  subst declaration
  obtain ⟨argument, expected, selected, parameterType, _, argumentTyped⟩ :=
    argumentsTyped.argument_at (by rw [box_shape.2.2.1]; rfl :
      boxDeclaration.params[0]? = some (.simple "workflow" (.base "Workflow")))
  have argumentEq : argument = workflow items := (Option.some.inj selected).symm
  have typeEq : expected = .base "Workflow" := (Option.some.inj parameterType).symm
  subst argument
  subst expected
  refine ⟨argumentTyped, ?_, ?_, argumentTyped.isWellScopedAt⟩
  · simpa only [boxed, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
      Bool.and_true] using typed.2.1
  · simpa only [boxed, isObjectPattern, isObjectPatternList, Bool.and_true] using typed.2.2.1

theorem workflow_items_place {permitted : Bool} {items : List Pattern}
    (typed : OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Workflow") (workflow items)) :
    ∀ item ∈ items, item = token "A" ∨ item = token "B" := by
  obtain ⟨declaration, member, labelEq, _, _, argumentsTyped⟩ := hasType_apply_inversion typed.1
  have parameterShape := flow_declaration_shape member labelEq.symm
  obtain ⟨argument, expected, selected, parameterType, _, argumentTyped⟩ :=
    argumentsTyped.argument_at (by rw [parameterShape]; rfl :
      declaration.params[0]? = some (.simple "marking" (.base "Marking")))
  have argumentEq : argument = marking items := (Option.some.inj selected).symm
  have typeEq : expected = .base "Marking" := (Option.some.inj parameterType).symm
  subst argument
  subst expected
  rcases hasType_collection_inversion argumentTyped with ⟨type, impossible, _⟩ |
    ⟨declaration, parameter, type, member, shape, category, elements⟩
  · cases impossible
  · have actual := marking_declaration_shape member (TypeExpr.base.inj category).symm
    rw [actual] at shape
    have elementEq : type = .base "Place" := by
      cases (List.cons.inj shape).1
      rfl
    subst type
    have objects : isObjectPatternList items = true := by
      simpa only [workflow, marking, isObjectPattern, isObjectPatternList,
        Bool.and_true, Bool.true_and, Option.isNone_none] using typed.2.2.1
    intro item member
    apply closed_place (elementsHaveType_iff.mp elements item member)
    obtain ⟨before, after, same⟩ := List.mem_iff_append.mp member
    rw [same] at objects
    exact isObjectPatternList_append_cons objects

private theorem append_cons_singleton {α : Type} {before after : List α} {middle only : α}
    (same : before ++ middle :: after = [only]) :
    before = [] ∧ middle = only ∧ after = [] := by
  have lengths := congrArg List.length same
  simp only [List.length_append, List.length_cons, List.length_nil] at lengths
  have beforeNil : before = [] := List.length_eq_zero_iff.mp (by omega)
  have afterNil : after = [] := List.length_eq_zero_iff.mp (by omega)
  subst before
  subst after
  exact ⟨rfl, (List.cons.inj same).1, rfl⟩

private theorem flow_not_in_token (context : OneHoleContext) (arguments : List Pattern)
    {label : String} (labelDifferent : label ≠ "Flow") :
    context.fill (.apply "Flow" arguments) ≠ token label := by
  intro same
  cases context with
  | hole => exact labelDifferent (Pattern.apply.inj same).1.symm
  | apply constructor before inner after =>
      have argumentsEq := (Pattern.apply.inj same).2
      have lengths := congrArg List.length argumentsEq
      simp only [List.length_append, List.length_cons, List.length_nil] at lengths
      omega
  | _ => cases same

private theorem flow_not_in_marking (context : OneHoleContext) (arguments : List Pattern)
    {items : List Pattern} (places : ∀ item ∈ items, item = token "A" ∨ item = token "B") :
    context.fill (.apply "Flow" arguments) ≠ marking items := by
  intro same
  cases context with
  | collection kind before inner after rest =>
      have elementsEq := (Pattern.collection.inj same).2.1
      have member : inner.fill (.apply "Flow" arguments) ∈ items := by
        rw [← elementsEq]
        exact List.mem_append_right _ List.mem_cons_self
      rcases places _ member with a | b
      · exact flow_not_in_token inner arguments (by decide : "A" ≠ "Flow") a
      · exact flow_not_in_token inner arguments (by decide : "B" ≠ "Flow") b
  | _ => cases same

private theorem flow_focus_in_workflow (context : OneHoleContext) (arguments : List Pattern)
    {items : List Pattern} (places : ∀ item ∈ items, item = token "A" ∨ item = token "B")
    (same : context.fill (.apply "Flow" arguments) = workflow items) :
    context = .hole ∧ .apply "Flow" arguments = workflow items := by
  cases context with
  | hole => exact ⟨rfl, same⟩
  | apply label before inner after =>
      obtain ⟨_, focusEq, _⟩ := append_cons_singleton (Pattern.apply.inj same).2
      exact False.elim (flow_not_in_marking inner arguments places focusEq)
  | _ => cases same

private theorem flow_focus_in_box (context : OneHoleContext) (arguments : List Pattern)
    {items : List Pattern} (places : ∀ item ∈ items, item = token "A" ∨ item = token "B")
    (same : context.fill (.apply "Flow" arguments) = boxed items) :
    context = boxContext ∧ .apply "Flow" arguments = workflow items := by
  cases context with
  | hole =>
      have labels := (Pattern.apply.inj same).1
      exact False.elim ((by decide : ("Flow" : String) ≠ "Box") labels)
  | apply label before inner after =>
      have labels := (Pattern.apply.inj same).1
      obtain ⟨beforeNil, focusEq, afterNil⟩ := append_cons_singleton (Pattern.apply.inj same).2
      obtain ⟨innerHole, focusEq⟩ := flow_focus_in_workflow inner arguments places focusEq
      subst label
      subst before
      subst after
      subst inner
      exact ⟨rfl, focusEq⟩
  | _ => cases same

/-- Every valid firing of a closed boxed workflow selects the outer workflow site. -/
theorem receipt_site_classification {permitted : Bool} {items : List Pattern}
    {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid (plan permitted) [] (.base "Workspace") (boxed items)) :
    receipt.job.ordinal = 0 ∧ receipt.job.site.context = boxContext ∧
      receipt.job.site.focus = workflow items ∧ receipt.job.site.focusBound = [] ∧
      receipt.job.site.focusType = .base "Workflow" ∧ receipt.job.site.address = [0] := by
  have position := List.mk_mem_zipIdx_iff_getElem?.mp valid.1.1
  have within := (List.getElem?_eq_some_iff.mp position).1
  have oneRule : (plan permitted).rules.length = 1 := by cases permitted <;> cbv
  have ordinal : receipt.job.ordinal = 0 := by rw [oneRule] at within; omega
  have sourceTyped := GeneralRuleReceiptSource.primitive_source_sorted valid
  have places := workflow_items_place (workflow_open_of_boxed sourceTyped)
  have flow : ∃ arguments, receipt.job.site.focus = .apply "Flow" arguments := by
    have firing := valid.2.1
    rw [ordinal] at firing
    cases firing with
    | @fire _ _ _ _ _ actualRule actualSpec _ _ _ _ declared _ _ _ matched _ _ _ _ =>
        have ruleEq : actualRule = rule :=
          Option.some.inj (declared.symm.trans (selected_rule permitted))
        subst actualRule
        have matching := matched.matching
        rw [rule_left] at matching
        generalize focusEq : receipt.job.site.focus = focus at matching ⊢
        cases matching with
        | constructor arguments => exact ⟨_, rfl⟩
  obtain ⟨arguments, focusShape⟩ := flow
  have zipperEq := valid.1.2.source_eq
  rw [focusShape] at zipperEq
  obtain ⟨contextEq, localEq⟩ := flow_focus_in_box receipt.job.site.context arguments places zipperEq
  have focusEq := focusShape.trans localEq
  have selected := valid.1.2.typedAt
  rw [contextEq] at selected
  obtain ⟨boundEq, typeEq⟩ := box_typedAt_indices selected
  refine ⟨ordinal, contextEq, focusEq, boundEq, typeEq, ?_⟩
  rw [valid.1.2.address_eq, contextEq]
  rfl

theorem receipt_to_box_contextual_instance {permitted : Bool} {items : List Pattern}
    {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid (plan permitted) [] (.base "Workspace") (boxed items)) :
    ∃ (site : TypedContextualEquationExecution.Site (environment permitted).language
        (environment permitted).free [] (.base "Workspace") [boxContext] (boxed items))
      (authoredReceipt : TypedContextualEquationExecution.Receipt),
      ContextualAuthoredEquationExecution.ContextualInstance (relations permitted)
        (environment permitted).language (environment permitted).free [] (.base "Workspace")
        [boxContext] (boxed items) 0 0 rule site authoredReceipt ∧
      authoredReceipt.atomic.captured = receipt.captured ∧
      authoredReceipt.atomic.completed = receipt.completed ∧
      authoredReceipt.atomic.target = receipt.localTarget ∧ authoredReceipt.target = receipt.target := by
  obtain ⟨ordinal, contextEq, focusEq, boundEq, typeEq, _⟩ := receipt_site_classification valid
  have firing : RootFiring (environment permitted) [] (.base "Workflow") (workflow items) 0
      receipt.matcherTrace receipt.captured receipt.completed receipt.premiseHistory receipt.localTarget := by
    simpa only [GeneralPlanEnvironment.environmentWith_empty, ordinal, focusEq, boundEq, typeEq] using valid.2.1
  obtain ⟨atomic, atomicValid, capturedEq, completedEq, targetEq⟩ :=
    guarded_root_to_conditional_instance firing
  refine ⟨boxSite permitted items (atomic_source_open atomicValid), boxedReceipt atomic,
    atomic_box_lift (atomic_source_open atomicValid) atomicValid, capturedEq, completedEq, targetEq, ?_⟩
  change boxContext.fill atomic.target = receipt.target
  rw [targetEq, valid.2.2.2.1, contextEq]

theorem box_contextual_instance_to_receipt {permitted : Bool} {items : List Pattern}
    {site : TypedContextualEquationExecution.Site (environment permitted).language
      (environment permitted).free [] (.base "Workspace") [boxContext] (boxed items)}
    {authoredReceipt : TypedContextualEquationExecution.Receipt}
    (valid : ContextualAuthoredEquationExecution.ContextualInstance (relations permitted)
      (environment permitted).language (environment permitted).free [] (.base "Workspace")
      [boxContext] (boxed items) 0 0 rule site authoredReceipt) :
    ∃ receipt : GeneralRuleJobs.Receipt,
      receipt.Valid (plan permitted) [] (.base "Workspace") (boxed items) ∧
      receipt.captured = authoredReceipt.atomic.captured ∧
      receipt.completed = authoredReceipt.atomic.completed ∧
      receipt.localTarget = authoredReceipt.atomic.target ∧ receipt.target = authoredReceipt.target := by
  have atomic := any_boxed_instance_to_atomic valid
  obtain ⟨trace, history, firing⟩ := conditional_instance_to_guarded_root atomic
  let declaration := (plan permitted).rules[0]'(by cases permitted <;> cbv)
  have declared : (plan permitted).rules[0]? = some declaration :=
    List.getElem?_eq_getElem (by cases permitted <;> cbv)
  let job : GeneralRuleJobs.Job := ⟨0, declaration, boxData items⟩
  have licensed : job.Valid (plan permitted) [] (.base "Workspace") (boxed items) :=
    ⟨List.mk_mem_zipIdx_iff_getElem?.mpr declared, box_licensed (atomic_source_open atomic)⟩
  have sourceTyped := atomic_source_open atomic
  have targetTyped := atomic_target_open atomic
  have outerTyped := (box_licensed sourceTyped).replace_checked authoredReceipt.atomic.target
    (box_accepts_replacement permitted items authoredReceipt.atomic.target) targetTyped.1
  have targetScope := outerTyped.isWellScopedAt
  have outerOpen : OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Workspace") (boxContext.fill authoredReceipt.atomic.target) := by
    refine ⟨outerTyped, ?_, ?_, targetScope⟩
    · simpa only [boxContext, OneHoleContext.fill, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, List.nil_append, Bool.and_true] using targetTyped.2.1
    · simpa only [boxContext, OneHoleContext.fill, isObjectPattern, isObjectPatternList,
        List.nil_append, Bool.and_true] using targetTyped.2.2.1
  let receipt : GeneralRuleJobs.Receipt :=
    ⟨job, trace, authoredReceipt.atomic.captured, authoredReceipt.atomic.completed, history,
      authoredReceipt.atomic.target, boxContext.fill authoredReceipt.atomic.target⟩
  refine ⟨receipt, ?_, rfl, rfl, rfl, ?_⟩
  · exact ⟨licensed, firing, box_accepts_replacement permitted items _, rfl, outerOpen⟩
  · exact (any_boxed_instance_readout valid).2.2.2.2.2.symm

theorem boxed_same_shape {items : List Pattern} {other : Pattern}
    (same : Same (boxed items) other) :
    ∃ others, other = boxed others ∧ Same (workflow items) (workflow others) := by
  obtain ⟨boxArguments, otherEq, boxSame⟩ := same_apply same
  subst other
  cases boxArguments with
  | nil => cases boxSame
  | cons inner after =>
      have afterNil : after = [] := List.map_eq_nil_iff.mp (List.cons.inj boxSame).2.symm
      subst after
      have workflowSame : Same (workflow items) inner := (List.cons.inj boxSame).1
      obtain ⟨flowArguments, innerEq, flowSame⟩ := same_apply workflowSame
      subst inner
      cases flowArguments with
      | nil => cases flowSame
      | cons markingOther after =>
          have afterNil : after = [] := List.map_eq_nil_iff.mp (List.cons.inj flowSame).2.symm
          subst after
          have markingSame : Same (marking items) markingOther := (List.cons.inj flowSame).1
          obtain ⟨others, markingEq, _⟩ := same_collection markingSame
          subst markingOther
          exact ⟨others, rfl, workflowSame⟩

theorem same_box_fill {left right : Pattern} (same : Same left right) :
    Same (boxContext.fill left) (boxContext.fill right) :=
  same_apply_congr "Box" (.cons same .nil)

def occurrenceCertificate (permitted : Bool) : CollectionOccurrenceAdmission.Certificate (plan permitted) :=
  ⟨by cases permitted <;> cbv⟩

theorem modelEquiv_of_same (permitted : Bool) {left right : Pattern} (same : Same left right) :
    Complete.Presented.ModelEquiv (plan permitted) [] (.base "Workspace") left right := by
  have first := Complete.Presented.canon_equiv (plan permitted) [] (.base "Workspace") left
  have second := Complete.Presented.canon_equiv (plan permitted) [] (.base "Workspace") right
  change canon left = canon right at same
  rw [same] at first
  exact .trans _ _ _ first (.symm _ _ second)

theorem presented_iff_box_contextual_instance (permitted : Bool) (items : List Pattern) (target : Pattern) :
    (Complete.Presented.gslt (plan permitted) [] (.base "Workspace")).Step (boxed items) target ↔
    ∃ (site : TypedContextualEquationExecution.Site (environment permitted).language
        (environment permitted).free [] (.base "Workspace") [boxContext] (boxed items))
      (receipt : TypedContextualEquationExecution.Receipt),
      ContextualAuthoredEquationExecution.ContextualInstance (relations permitted)
        (environment permitted).language (environment permitted).free [] (.base "Workspace")
        [boxContext] (boxed items) 0 0 rule site receipt ∧ Same target receipt.target := by
  constructor
  · rintro ⟨representative, original, before, valid, after⟩
    have ready := (occurrenceCertificate permitted).requirements
    have beforeSame : Same (boxed items) representative := CollectionRootSearch.modelEquiv_canon
      (.base "Workspace") ready.noEquations ready.noLaws ready.noExtrusions before
    have afterSame : Same original.target target := CollectionRootSearch.modelEquiv_canon
      (.base "Workspace") ready.noEquations ready.noLaws ready.noExtrusions after
    obtain ⟨others, representativeEq, workflowSame⟩ := boxed_same_shape beforeSame
    subst representative
    obtain ⟨ordinal, contextEq, focusEq, boundEq, typeEq, _⟩ := receipt_site_classification valid
    have firing : RootFiring (environment permitted) [] (.base "Workflow") (workflow others) 0
        original.matcherTrace original.captured original.completed original.premiseHistory original.localTarget := by
      simpa only [GeneralPlanEnvironment.environmentWith_empty, ordinal, focusEq, boundEq, typeEq]
        using valid.2.1
    obtain ⟨trace, assignment, localTarget, firing, localSame⟩ :=
      guarded_root_same_source workflowSame.symm firing
    obtain ⟨site, receipt, authoredValid, _, targetEq⟩ :=
      (guarded_root_iff_exists_box_contextual_instance permitted items localTarget).mp
        ⟨trace, assignment, assignment, original.premiseHistory, firing⟩
    refine ⟨site, receipt, authoredValid, ?_⟩
    change canon target = canon receipt.target
    calc
      canon target = canon original.target := afterSame.symm
      _ = canon (boxContext.fill original.localTarget) := by rw [valid.2.2.2.1, contextEq]
      _ = canon (boxContext.fill localTarget) := same_box_fill localSame
      _ = canon receipt.target := congrArg canon targetEq.symm
  · rintro ⟨site, receipt, authoredValid, same⟩
    obtain ⟨original, valid, _, _, _, targetEq⟩ := box_contextual_instance_to_receipt authoredValid
    refine ⟨boxed items, original, .refl _, valid, ?_⟩
    apply modelEquiv_of_same permitted
    rw [targetEq]
    exact same.symm

/-- The actual retained Search and the independently permitted Box rule have the same successor classes. -/
theorem search_iff_box_contextual_instance (permitted : Bool) (depth : Nat)
    (items : List Pattern) (target : Pattern) :
    (∃ work receipt, receipt ∈
        (CollectionOccurrenceSearch.search (plan permitted) [] (.base "Workspace") depth).publication
          ((CollectionOccurrenceSearch.search (plan permitted) [] (.base "Workspace") depth).run
            (boxed items) work) ∧ Same target receipt.target) ↔
    ∃ (site : TypedContextualEquationExecution.Site (environment permitted).language
        (environment permitted).free [] (.base "Workspace") [boxContext] (boxed items))
      (receipt : TypedContextualEquationExecution.Receipt),
      ContextualAuthoredEquationExecution.ContextualInstance (relations permitted)
        (environment permitted).language (environment permitted).free [] (.base "Workspace")
        [boxContext] (boxed items) 0 0 rule site receipt ∧ Same target receipt.target :=
  (CollectionOccurrenceAdmission.source_exact (occurrenceCertificate permitted) [] (.base "Workspace")
    depth (boxed items) target).symm.trans (presented_iff_box_contextual_instance permitted items target)

theorem permitted_sample_search (depth : Nat) :
    ∃ work receipt, receipt ∈
      (CollectionOccurrenceSearch.search (plan true) [] (.base "Workspace") depth).publication
        ((CollectionOccurrenceSearch.search (plan true) [] (.base "Workspace") depth).run
          (boxed sampleItems) work) ∧ Same (boxContext.fill sampleTarget) receipt.target := by
  obtain ⟨site, receipt, valid, _, _, _, targetEq⟩ := permitted_sample_box
  apply (search_iff_box_contextual_instance true depth sampleItems (boxContext.fill sampleTarget)).mpr
  exact ⟨site, receipt, valid, congrArg canon targetEq.symm⟩

theorem refused_search {items : List Pattern} (depth work : Nat) {receipt : GeneralRuleJobs.Receipt}
    (published : receipt ∈
      (CollectionOccurrenceSearch.search (plan false) [] (.base "Workspace") depth).publication
        ((CollectionOccurrenceSearch.search (plan false) [] (.base "Workspace") depth).run
          (boxed items) work)) : False := by
  obtain ⟨site, authoredReceipt, valid, _⟩ :=
    (search_iff_box_contextual_instance false depth items receipt.target).mp
      ⟨work, receipt, published, rfl⟩
  exact refused_box_instance valid

#print axioms rule_left
#print axioms rule_match_comparison
#print axioms guarded_match_same
#print axioms typed_assignment_same
#print axioms guarded_root_same_source
#print axioms place_declaration_shape
#print axioms flow_declaration_shape
#print axioms marking_declaration_shape
#print axioms closed_place
#print axioms workflow_open_of_boxed
#print axioms workflow_items_place
#print axioms receipt_site_classification
#print axioms receipt_to_box_contextual_instance
#print axioms box_contextual_instance_to_receipt
#print axioms boxed_same_shape
#print axioms same_box_fill
#print axioms occurrenceCertificate
#print axioms modelEquiv_of_same
#print axioms presented_iff_box_contextual_instance
#print axioms search_iff_box_contextual_instance
#print axioms permitted_sample_search
#print axioms refused_search

end Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.SearchAgreement

/-!
# Proper authored collection wrappers and operational source joins

The source constructors below fix the declared HashBag wrapper shape. The
wrong-kind control separates slot-directed representation lowering from
source eligibility. Typed joins derive captured and result typing from the
source; the permitted Box context remains explicit.
-/

namespace Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.AuthoredAgreement

set_option maxHeartbeats 1600000

open Mettapedia.OSLF.MeTTaIL Syntax Match Engine CoreReduction ReferenceStep

def sourceRule : RewriteRule := authored.rewrites[0]'(by cbv)

def wrappedMarking (items : List Pattern) : Pattern :=
  .apply "Tokens" [.collection .hashBag items none]

def wrappedWorkflow (items : List Pattern) : Pattern :=
  .apply "Flow" [wrappedMarking items]

def wrappedBox (items : List Pattern) : Pattern :=
  .apply "Box" [wrappedWorkflow items]

def lower : Pattern → Pattern := unwrap (bareLabels authored)

theorem source_rule_selected : authored.rewrites = [sourceRule] := by cbv
theorem bare_labels : bareLabels authored = [("Tokens", .hashBag)] := by cbv
theorem source_rule_left : sourceRule.left =
    .apply "Flow" [.apply "Tokens" [.collection .hashBag [token "A"] (some "rest")]] := by cbv
theorem source_rule_right : sourceRule.right =
    .apply "Flow" [.apply "Tokens" [.collection .hashBag [token "B"] (some "rest")]] := by cbv
theorem source_rule_premises : sourceRule.premises = [.relationQuery "permit" []] := by cbv
theorem core_rule_left : RootAgreement.rule.left =
    .apply "Flow" [.collection .hashBag [token "A"] (some "rest")] := by cbv
theorem core_rule_right : RootAgreement.rule.right =
    .apply "Flow" [.collection .hashBag [token "B"] (some "rest")] := by cbv
theorem core_rule_premises : RootAgreement.rule.premises = [.relationQuery "permit" []] := by cbv

theorem lowers_marking (items : List Pattern) :
    lower (wrappedMarking items) = marking (items.map lower) := by
  simp [lower, wrappedMarking, bare_labels, unwrap, marking]

theorem lowers_workflow (items : List Pattern) :
    lower (wrappedWorkflow items) = workflow (items.map lower) := by
  simp [lower, wrappedWorkflow, wrappedMarking, bare_labels, unwrap, workflow, marking,
    List.lookup]

theorem lowers_box (items : List Pattern) :
    lower (wrappedBox items) = boxed (items.map lower) := by
  simp [lower, wrappedBox, wrappedWorkflow, wrappedMarking, bare_labels, unwrap,
    boxed, workflow, marking, List.lookup]

theorem match_unary (label : String) (schema target : Pattern) :
    matchPattern (.apply label [schema]) (.apply label [target]) =
      matchPattern schema target := by
  simp [matchPattern, matchArgs, mergeBindings]

theorem matches_exact (items : List Pattern) :
    matchPattern sourceRule.left (wrappedWorkflow items) =
      matchPattern RootAgreement.rule.left (workflow items) := by
  rw [source_rule_left, core_rule_left]
  simp only [wrappedWorkflow, wrappedMarking, workflow, marking,
    match_unary]

theorem origin_indices_exact (items : List Pattern) :
    (matchPattern sourceRule.left (wrappedWorkflow items)).zipIdx =
      (matchPattern RootAgreement.rule.left (workflow items)).zipIdx := by
  rw [matches_exact]

theorem lower_token («name» : String) : lower (token «name») = token «name» := by
  simp only [lower, bare_labels, token, unwrap, List.map_nil]
  cases found : List.lookup «name» [("Tokens", CollType.hashBag)] <;> rfl

theorem lowered_reduct (rest : List Pattern) :
    lower (applyBindings [("rest", marking rest)] sourceRule.right) =
      workflow (token "B" :: rest.map lower) := by
  rw [source_rule_right]
  simp [applyBindings, marking, lower, bare_labels, unwrap, workflow, token, List.lookup]

theorem core_reduct (rest : List Pattern) :
    applyBindings [("rest", marking rest)] RootAgreement.rule.right =
      workflow (token "B" :: rest) := by
  rw [core_rule_right]
  simp [applyBindings, marking, workflow, token]

theorem instantiated_square (rest : List Pattern) :
    lower (applyBindings [("rest", marking rest)] sourceRule.right) =
      applyBindings [("rest", marking (rest.map lower))] RootAgreement.rule.right := by
  rw [lowered_reduct, core_reduct]

theorem match_token (label : String) (target : Pattern) :
    matchPattern (token label) target = if target = token label then [[]] else [] := by
  cases target <;> simp [token, matchPattern]
  case apply actual arguments =>
    cases arguments <;> simp [matchArgs, eq_comm]

theorem source_matches (items : List Pattern) :
    matchPattern sourceRule.left (wrappedWorkflow items) =
      items.zipIdx.flatMap fun (value, index) =>
        if value = token "A" then [[("rest", marking (items.eraseIdx index))]] else [] := by
  rw [matches_exact, core_rule_left]
  simp only [workflow, marking, match_unary, matchPattern, beq_self_eq_true,
    ↓reduceIte]
  simp only [matchBag]
  apply List.flatMap_congr
  rintro ⟨value, index⟩ _
  rw [match_token]
  split <;> simp [mergeBindings]

theorem source_reduct (rest : List Pattern) :
    applyBindings [("rest", marking rest)] sourceRule.right =
      wrappedWorkflow (token "B" :: rest) := by
  rw [source_rule_right]
  simp [applyBindings, marking, wrappedWorkflow, wrappedMarking, token]

theorem permit_query (permitted : Bool) (lang : LanguageDef) (seed : Bindings) :
    premiseStepWithEnv (RootAgreement.relations permitted) lang seed
      (.relationQuery "permit" []) = if permitted then [seed] else [] := by
  cases permitted <;>
    simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
      RootAgreement.relations, RootAgreement.provider_rows, matchRelationArgs,
      mergeBindings]

theorem permit_premises (permitted : Bool) (lang : LanguageDef) (seed : Bindings) :
    applyPremisesWithEnv (RootAgreement.relations permitted) lang
      [.relationQuery "permit" []] seed = if permitted then [seed] else [] := by
  simp [applyPremisesWithEnv, permit_query]

theorem guarded_application (permitted : Bool) (lang : LanguageDef)
    (rule : RewriteRule) (source : Pattern)
    (premises : rule.premises = [.relationQuery "permit" []])
    (aligned : ruleDepthAligned rule = true) :
    applyRuleWithPremisesUsing (RootAgreement.relations permitted) lang rule source =
      if permitted then (matchPattern rule.left source).map
        (fun bindings => applyBindings bindings rule.right) else [] := by
  simp only [applyRuleWithPremisesUsing,
    ReflectiveCanonical.matchPatternForRule_eq_syntactic, premises, permit_premises]
  cases permitted with
  | false => simp
  | true =>
      simp only [↓reduceIte, ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
        List.map_singleton, ← List.map_eq_flatMap]
      apply List.map_congr_left
      intro bindings _
      exact applyRuleBindings_eq_applyBindings rule bindings aligned

theorem source_steps (permitted : Bool) (items : List Pattern) :
    rewriteStepWithPremisesUsing (RootAgreement.relations permitted) authored
      (wrappedWorkflow items) =
      if permitted then items.zipIdx.flatMap (fun (value, index) =>
        if value = token "A" then [wrappedWorkflow (token "B" :: items.eraseIdx index)]
        else []) else [] := by
  simp only [rewriteStepWithPremisesUsing, source_rule_selected, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  rw [guarded_application permitted authored sourceRule _ source_rule_premises (by cbv)]
  rw [source_matches]
  cases permitted <;> simp only [Bool.false_eq_true, ↓reduceIte]
  rw [List.map_flatMap]
  apply List.flatMap_congr
  rintro ⟨value, index⟩ _
  split <;> simp [source_reduct]

theorem core_steps (permitted : Bool) (items : List Pattern) :
    rewriteStepWithPremisesUsing (RootAgreement.relations permitted) language
      (workflow items) =
      if permitted then items.zipIdx.flatMap (fun (value, index) =>
        if value = token "A" then [workflow (token "B" :: items.eraseIdx index)]
        else []) else [] := by
  have selected : language.rewrites = [RootAgreement.rule] := by cbv
  simp only [rewriteStepWithPremisesUsing, selected, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  rw [guarded_application permitted language RootAgreement.rule _ core_rule_premises (by cbv)]
  rw [← matches_exact, source_matches]
  cases permitted <;> simp only [Bool.false_eq_true, ↓reduceIte]
  rw [List.map_flatMap]
  apply List.flatMap_congr
  rintro ⟨value, index⟩ _
  split <;> simp [core_reduct]

theorem lower_token_iff («name» : String) (pattern : Pattern) :
    lower pattern = token «name» ↔ pattern = token «name» := by
  cases pattern <;> simp [lower, bare_labels, unwrap, token]
  case apply label arguments =>
    cases found : List.lookup label [("Tokens", CollType.hashBag)] with
    | none => simp
    | some kind =>
        have labelEq : label = "Tokens" := by
          cases comparison : (label == "Tokens") with
          | false => simp [List.lookup, comparison] at found
          | true => exact beq_iff_eq.mp comparison
        subst label
        cases arguments with
        | nil => simp
        | cons first rest =>
          cases rest with
          | cons second rest => simp
          | nil =>
              cases result : unwrap [("Tokens", CollType.hashBag)] first <;>
                simp [result]

theorem guarded_execution_square (permitted : Bool) (items : List Pattern) :
    (rewriteStepWithPremisesUsing (RootAgreement.relations permitted) authored
      (wrappedWorkflow items)).map lower =
      rewriteStepWithPremisesUsing (RootAgreement.relations permitted) language
        (lower (wrappedWorkflow items)) := by
  rw [source_steps, lowers_workflow, core_steps]
  cases permitted <;> simp only [Bool.false_eq_true, ↓reduceIte, List.map_nil]
  rw [List.map_flatMap, List.zipIdx_map, List.flatMap_map]
  apply List.flatMap_congr
  rintro ⟨value, index⟩ _
  by_cases selected : value = token "A"
  · simp [selected, lower_token, lowers_workflow, List.eraseIdx_map]
  · simp [selected, (lower_token_iff "A" value).not.mpr selected]

theorem actual_rule_reduction :
    reduceRewrite (canonicalGrammar authored) sourceRule = .ok RootAgreement.rule := by cbv

theorem actual_left_reduction : lower sourceRule.left = RootAgreement.rule.left := by cbv

theorem actual_right_reduction : lower sourceRule.right = RootAgreement.rule.right := by cbv

theorem rule_origin_retained : sourceRule.«name» = RootAgreement.rule.«name» := by cbv

theorem no_equations_discarded : authored.equations = [] ∧ language.equations = [] := by cbv

theorem nullary_premises_iff (rel : RelationEnv) (lang : LanguageDef)
    (sites : Pattern) (initial final : Bindings) (witnesses : List Witness) :
    PremisesValid rel lang sites initial [.relationQuery "permit" []] witnesses final →
      final ∈ premiseStepWithEnv rel lang initial (.relationQuery "permit" []) := by
  intro held
  cases held with
  | cons first tail =>
      cases tail
      cases first with
      | base _ member => exact member
      | step endpoints _ _ _ => simp [stepEndpoints] at endpoints

theorem reference_iff_engine (rel : RelationEnv) (lang : LanguageDef)
    (rule : RewriteRule) (source target : Pattern)
    (selected : lang.rewrites = [rule])
    (premises : rule.premises = [.relationQuery "permit" []])
    (binderFree : Match.binderFree rule.right = true) :
    Step rel lang source target ↔
      target ∈ applyRuleWithPremisesUsing rel lang rule source := by
  constructor
  · rintro ⟨witness, valid⟩
    cases valid with
    | @rule source index actual initial final witnesses declared matched held =>
        have actualEq : actual = rule := by
          rw [selected] at declared
          cases index with
          | zero => simpa using declared.symm
          | succ index => simp at declared
        cases actualEq
        rw [premises] at held
        have finalMember := nullary_premises_iff rel lang _ initial final witnesses held
        simp only [applyRuleWithPremisesUsing, ReflectiveCanonical.matchPatternForRule_eq_syntactic,
          List.mem_flatMap, List.mem_map]
        refine ⟨initial, ?_, final, ?_, ?_⟩
        · simpa using matched
        · simpa [applyPremisesWithEnv, premises] using finalMember
        · rw [ReflectiveSubstitution.applyBindingsForRule_eq_syntactic, applyRuleBindings,
            applyBindingsScoped_zero_of_binderFree _ _ _ binderFree,
            applyBindingsScoped_zero_of_binderFree _ _ _ binderFree]
  · simp only [applyRuleWithPremisesUsing, ReflectiveCanonical.matchPatternForRule_eq_syntactic,
      List.mem_flatMap, List.mem_map]
    rintro ⟨initial, matched, final, held, targetEq⟩
    have member : final ∈ premiseStepWithEnv rel lang initial (.relationQuery "permit" []) := by
      simpa [applyPremisesWithEnv, premises] using held
    have valid : PremisesValid rel lang (captureSites rule) initial rule.premises [.base final] final := by
      rw [premises]
      exact .cons (.base rfl member) (.nil final)
    have result := StepValid.rule (relEnv := rel) (language := lang) (source := source)
      (index := 0) (rule := rule) (by simp [selected]) (by simpa using matched) valid
    refine ⟨.rule 0 initial [.base final], ?_⟩
    have computed : ReflectiveSubstitution.applyBindingsForRule lang rule final =
        applyBindingsScoped (captureSites rule) final 0 rule.right := by
      rw [ReflectiveSubstitution.applyBindingsForRule_eq_syntactic, applyRuleBindings,
        applyBindingsScoped_zero_of_binderFree _ _ _ binderFree,
        applyBindingsScoped_zero_of_binderFree _ _ _ binderFree]
    rw [← computed, targetEq] at result
    exact result


theorem authored_reference_iff_engine (permitted : Bool) (source target : Pattern) :
    Step (RootAgreement.relations permitted) authored source target ↔
      target ∈ rewriteStepWithPremisesUsing (RootAgreement.relations permitted) authored source := by
  rw [reference_iff_engine _ authored sourceRule source target source_rule_selected
    source_rule_premises (by cbv)]
  simp [rewriteStepWithPremisesUsing, source_rule_selected]

theorem core_reference_iff_engine (permitted : Bool) (source target : Pattern) :
    Step (RootAgreement.relations permitted) language source target ↔
      target ∈ rewriteStepWithPremisesUsing (RootAgreement.relations permitted) language source := by
  have selected : language.rewrites = [RootAgreement.rule] := by cbv
  rw [reference_iff_engine _ language RootAgreement.rule source target selected
    core_rule_premises (by cbv)]
  simp [rewriteStepWithPremisesUsing, selected]

theorem authored_reference_iff_core_reference (permitted : Bool)
    (items : List Pattern) (output : Pattern) :
    (∃ target, Step (RootAgreement.relations permitted) authored (wrappedWorkflow items) target ∧
      lower target = output) ↔
      Step (RootAgreement.relations permitted) language (lower (wrappedWorkflow items)) output := by
  rw [core_reference_iff_engine, ← guarded_execution_square]
  simp only [List.mem_map]
  constructor
  · rintro ⟨target, stepped, endpoint⟩
    exact ⟨target, (authored_reference_iff_engine _ _ _).mp stepped, endpoint⟩
  · rintro ⟨target, published, endpoint⟩
    exact ⟨target, (authored_reference_iff_engine _ _ _).mpr published, endpoint⟩

theorem refused_source (items : List Pattern) :
    rewriteStepWithPremisesUsing (RootAgreement.relations false) authored
      (wrappedWorkflow items) = [] := by rw [source_steps]; rfl

theorem permitted_equal_tokens :
    rewriteStepWithPremisesUsing (RootAgreement.relations true) authored
      (wrappedWorkflow [token "A", token "A", token "B"]) =
      [wrappedWorkflow [token "B", token "A", token "B"],
       wrappedWorkflow [token "B", token "A", token "B"]] := by
  rw [source_steps]
  cbv

theorem wrong_wrapper_refused (items : List Pattern) :
    rewriteStepWithPremisesUsing (RootAgreement.relations true) authored
      (.apply "Flow" [.apply "Other" [marking items]]) = [] := by
  simp only [rewriteStepWithPremisesUsing, source_rule_selected, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  rw [guarded_application true authored sourceRule _ source_rule_premises (by cbv)]
  rw [source_rule_left]
  simp [match_unary, matchPattern]

def malformedWrapper : Pattern :=
  .apply "Flow" [.apply "Tokens" [token "A"]]

def wrongKindWrapper : Pattern :=
  .apply "Flow" [.apply "Tokens" [.collection .vec [token "A"] none]]

theorem malformed_wrapper_retained : lower malformedWrapper = malformedWrapper := by cbv

theorem malformed_wrapper_refused :
    rewriteStepWithPremisesUsing (RootAgreement.relations true) authored malformedWrapper = [] ∧
      rewriteStepWithPremisesUsing (RootAgreement.relations true) language
        (lower malformedWrapper) = [] := by cbv

theorem wrong_kind_declaration_assigns_carrier :
    lower wrongKindWrapper = workflow [token "A"] := by cbv

theorem wrong_kind_separates_raw_presentations :
    rewriteStepWithPremisesUsing (RootAgreement.relations true) authored wrongKindWrapper = [] ∧
      rewriteStepWithPremisesUsing (RootAgreement.relations true) language
        (lower wrongKindWrapper) = [workflow [token "B"]] := by cbv

theorem raw_wrappers_are_not_core_inputs :
    WellSorted.checkOpenPatternWellSorted language (WellSorted.FreeTypeContext.ofList []) [] (.base "Workflow")
        (wrappedWorkflow [token "A"]) = false ∧
      WellSorted.checkOpenPatternWellSorted language (WellSorted.FreeTypeContext.ofList []) [] (.base "Workflow")
        malformedWrapper = false ∧
      WellSorted.checkOpenPatternWellSorted language (WellSorted.FreeTypeContext.ofList []) [] (.base "Workflow")
        wrongKindWrapper = false := by cbv

theorem lowered_wrong_kind_passes_core_check :
    WellSorted.checkOpenPatternWellSorted language (WellSorted.FreeTypeContext.ofList []) [] (.base "Workflow")
      (lower wrongKindWrapper) = true := by cbv

theorem lower_box_context (term : Pattern) :
    lower (.apply "Box" [term]) = .apply "Box" [lower term] := by
  simp [lower, bare_labels, unwrap, List.lookup]

theorem boxed_execution_square (permitted : Bool) (items : List Pattern) :
    ((rewriteStepWithPremisesUsing (RootAgreement.relations permitted) authored
      (wrappedWorkflow items)).map (fun target => .apply "Box" [target])).map lower =
      (rewriteStepWithPremisesUsing (RootAgreement.relations permitted) language
        (lower (wrappedWorkflow items))).map (fun target => .apply "Box" [target]) := by
  rw [← guarded_execution_square]
  simp only [List.map_map]
  apply List.map_congr_left
  intro target _
  exact lower_box_context target

open RuleBinding ScopedRuleMatching GeneralScopedMatch
open Mettapedia.GSLT.LanguageDef.WellSorted
open CollectionNestedConsumerControls.RootAgreement
open GeneralTypedOccurrence
open CanonicalBags

theorem environment_language (permitted : Bool) : (environment permitted).language = language := by
  cases permitted <;> cbv

def restAssignment (items : List Pattern) : ScopedRuleMatching.Assignment :=
  [("rest", ⟨[], 0, marking items⟩)]

theorem recovery_identity : recoveryAssignment 0 0 0 [] = Pattern.bvar := by
  funext index
  simp [recoveryAssignment]

theorem occurrence_identity : occurrenceAssignment 0 0 [] = Pattern.bvar := by
  funext index
  simp [occurrenceAssignment]

theorem recover_root {target : Pattern} (inScope : target.isWellScopedAt 0 = true) :
    recoverValue? [] 0 0 [] target = some ⟨[], 0, target⟩ := by
  simp [recoverValue?, inScope, variableSpine?, recovery_identity, instantiateValue?,
    occurrence_identity, ContextSubstitution.substitute_id]

theorem instantiate_root {target : Pattern} (inScope : target.isWellScopedAt 0 = true) :
    instantiateValue? ⟨[], 0, target⟩ 0 0 [] = some target := by
  simp [instantiateValue?, inScope, occurrence_identity, ContextSubstitution.substitute_id]

theorem rest_capture (items : List Pattern)
    (inScope : (marking items).isWellScopedAt 0 = true) :
    captureRest? rule specification 0 0 .left [0, 1] [] "rest" .hashBag items =
      some (restAssignment items) := by
  have dependencies : dependencies? specification "rest" = some [] := by cbv
  have arguments : arguments? rule specification "rest" .left [0, 1] = some [] := by cbv
  simp only [captureRest?, capture?, dependencies, arguments]
  change (recoverValue? [] 0 0 [] (marking items)).bind (fun value => assign [] "rest" value) = _
  rw [recover_root inScope]
  rfl

theorem scoped_match_selected {items : List Pattern} (selected : Nat)
    (within : selected < items.length) (chosen : items[selected] = token "A")
    (inScope : (marking (items.eraseIdx selected)).isWellScopedAt 0 = true) :
    Matches rule specification 0 .left [] 0 [] rule.left (workflow items)
      (restAssignment (items.eraseIdx selected)) := by
  rw [core_rule_left]
  apply Matches.constructor
  apply Arguments.cons
  · apply Matches.bag (by decide)
    apply Bag.cons selected within
    · rw [chosen]
      exact Matches.constructor Arguments.nil
    · apply Bag.rest
      simpa using rest_capture (items.eraseIdx selected) inScope
  · exact Arguments.nil


theorem places_properties (items : List Pattern)
    (places : ∀ item ∈ items, item = token "A" ∨ item = token "B") :
    Pattern.hasCanonicalBinderMetadataList items = true ∧
      isObjectPatternList items = true ∧ Pattern.isWellScopedListAt 0 items = true := by
  induction items with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons head tail ih =>
      have rest := ih (fun item member => places item (.tail _ member))
      rcases places head (.head _) with rfl | rfl <;>
        simpa only [Pattern.hasCanonicalBinderMetadataList, Pattern.hasCanonicalBinderMetadata,
          isObjectPatternList, isObjectPattern, Pattern.isWellScopedListAt,
          Pattern.isWellScopedAt, token, Bool.true_and] using rest

theorem places_erased {items : List Pattern} (index : Nat)
    (places : ∀ item ∈ items, item = token "A" ∨ item = token "B") :
    ∀ item ∈ items.eraseIdx index, item = token "A" ∨ item = token "B" :=
  fun item member => places item (List.mem_of_mem_eraseIdx member)

theorem marking_scope_of_places (items : List Pattern)
    (places : ∀ item ∈ items, item = token "A" ∨ item = token "B") :
    (marking items).isWellScopedAt 0 = true := by
  simpa only [marking, Pattern.isWellScopedAt] using (places_properties items places).2.2

theorem token_a_open (permitted : Bool) :
    OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Place") (token "A") := by
  apply checkOpenPatternWellSorted_sound
  cases permitted <;> cbv

theorem token_b_open (permitted : Bool) :
    OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Place") (token "B") := by
  apply checkOpenPatternWellSorted_sound
  cases permitted <;> cbv

def markingDeclaration : GrammarRule := (environment true).language.terms[2]'(by cbv)
def flowDeclaration : GrammarRule := (environment true).language.terms[3]'(by cbv)

theorem marking_declaration (permitted : Bool) :
    markingDeclaration ∈ (environment permitted).language.terms := by
  cases permitted <;> cbv <;> exact .tail _ (.tail _ (.head _))

theorem flow_declaration (permitted : Bool) :
    flowDeclaration ∈ (environment permitted).language.terms := by
  cases permitted <;> cbv <;> exact .tail _ (.tail _ (.tail _ (.head _)))

theorem marking_decl_shape : markingDeclaration.bareParams =
    [.simple "items" (.collection .hashBag (.base "Place"))] := by cbv

theorem marking_decl_category : markingDeclaration.category = "Marking" := by cbv

theorem flow_decl_parameters : flowDeclaration.params = [.simple "marking" (.base "Marking")] := by cbv
theorem flow_decl_label : flowDeclaration.label = "Flow" := by cbv
theorem flow_decl_category : flowDeclaration.category = "Workflow" := by cbv
theorem flow_decl_bare : flowDeclaration.bareParams = [.simple "marking" (.base "Marking")] := by cbv

theorem marking_typed_of_places (permitted : Bool) (items : List Pattern)
    (places : ∀ item ∈ items, item = token "A" ∨ item = token "B") :
    HasType (environment permitted).language (environment permitted).free []
      (marking items) (.base "Marking") := by
  have elements : ElementsHaveType (environment permitted).language (environment permitted).free []
      items (.base "Place") := by
    apply elementsHaveType_iff.mpr
    intro item member
    rcases places item member with rfl | rfl
    · exact (token_a_open permitted).1
    · exact (token_b_open permitted).1
  simpa only [marking, marking_decl_category] using
    (HasType.collectionConstructor (rule := markingDeclaration) (rest := none)
      (marking_declaration permitted) marking_decl_shape elements)

theorem workflow_open_of_places (permitted : Bool) (items : List Pattern)
    (places : ∀ item ∈ items, item = token "A" ∨ item = token "B") :
    OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Workflow") (workflow items) := by
  have ordinary : ¬ UsesBareCollection flowDeclaration := by
    rintro ⟨«name», kind, element, shape⟩
    rw [flow_decl_bare] at shape
    cases (List.cons.inj shape).1
  have arguments : ArgumentsHaveTypes (environment permitted).language (environment permitted).free []
      [marking items] flowDeclaration.params := by
    rw [flow_decl_parameters]
    exact .cons trivial rfl (marking_typed_of_places permitted items places) .nil
  have typed : HasType (environment permitted).language (environment permitted).free []
      (workflow items) (.base "Workflow") := by
    simpa only [workflow, flow_decl_label, flow_decl_category] using
      HasType.constructor (flow_declaration permitted) ordinary arguments
  have properties := places_properties items places
  refine ⟨typed, ?_, ?_, typed.isWellScopedAt⟩
  · simpa only [workflow, marking, Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList, Bool.and_true] using properties.1
  · simpa only [workflow, marking, isObjectPattern, isObjectPatternList,
      Option.isNone_none, Bool.true_and, Bool.and_true] using properties.2.1

theorem atom_scoped_match (target : Pattern) :
    matchAtWith literalBodyComparison rule specification 0 .left [0, 0] 0 []
      (token "A") target = if target = token "A" then [[]] else [] := by
  cases target <;> simp [token, matchAtWith]
  case apply label arguments =>
    cases arguments <;> simp [matchArgsAtWith, eq_comm]

theorem scoped_matches (items : List Pattern)
    (places : ∀ item ∈ items, item = token "A" ∨ item = token "B") :
    matchRuleAt rule specification 0 (workflow items) =
      items.zipIdx.flatMap (fun (value, index) =>
        if value = token "A" then [restAssignment (items.eraseIdx index)] else []) := by
  simp only [matchRuleAt, matchRuleWithAt, core_rule_left, workflow, marking, matchAtWith,
    beq_self_eq_true, ↓reduceIte, matchArgsAtWith, List.nil_append,
    Option.isNone_none, Bool.and_true]
  simp only [matchBagAtWith]
  have notVector : (CollType.hashBag == CollType.vec) = false := rfl
  simp only [notVector, Bool.false_eq_true, ↓reduceIte, ← List.map_eq_flatMap,
    List.cons_append, List.nil_append, Nat.zero_add]
  simp only [List.map_id']
  apply List.flatMap_congr
  rintro ⟨value, index⟩ member
  dsimp only
  rw [atom_scoped_match]
  split
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [captureRestWith?_literal]
    rw [rest_capture (items.eraseIdx index)
      (marking_scope_of_places _ (places_erased index places))]
    rfl
  · rfl


theorem rest_assignment_typed (permitted : Bool) (items : List Pattern)
    (places : ∀ item ∈ items, item = token "A" ∨ item = token "B") :
    GeneralPremise.TypedAssignment (environment permitted) context (restAssignment items) := by
  have elements : ElementsHaveType (environment permitted).language (environment permitted).free []
      items (.base "Place") := by
    apply elementsHaveType_iff.mpr
    intro item member
    rcases places item member with rfl | rfl
    · exact (token_a_open permitted).1
    · exact (token_b_open permitted).1
  constructor
  · intro «name» value member
    have pair := List.mem_singleton.mp member
    have named : «name» = "rest" := (Prod.mk.inj pair).1
    have body : value = ⟨[], 0, marking items⟩ := (Prod.mk.inj pair).2
    subst «name»
    subst value
    refine ⟨[], .collection .hashBag (.base "Place"), ?_, ?_, rfl, rfl, ?_⟩
    · cbv
    · cbv
    · exact HasType.collection elements
  · intro «name» value member
    have pair := List.mem_singleton.mp member
    have body : value = ⟨[], 0, marking items⟩ := (Prod.mk.inj pair).2
    subst value
    simpa only [marking, isObjectPattern, Option.isNone_none, Bool.true_and] using
      (places_properties items places).2.1

theorem rest_reduct (items : List Pattern)
    (inScope : (marking items).isWellScopedAt 0 = true) :
    reduct? rule specification 0 (restAssignment items) =
      some (workflow (token "B" :: items)) := by
  have arguments : arguments? rule specification "rest" .right [0, 1] = some [] := by cbv
  simp only [reduct?, instantiateAt?, core_rule_right, instantiateWith?, instantiateArgsWith?,
    token, restAssignment, lookup, List.find?_cons, beq_self_eq_true,
    Option.map_some,
    List.nil_append, List.cons_append, List.length_cons, List.length_nil,
    Nat.zero_add, arguments]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [instantiate_root inScope]
  rfl

def SelectedResult (items : List Pattern) (target : Pattern) : Prop :=
  ∃ (value : Pattern) (index : Nat), (value, index) ∈ items.zipIdx ∧
    value = token "A" ∧ target = workflow (token "B" :: items.eraseIdx index)

theorem reference_iff_selection (permitted : Bool) (items : List Pattern) (target : Pattern) :
    ReferenceStep.Step (relations permitted) language (workflow items) target ↔
      permitted = true ∧ SelectedResult items target := by
  rw [core_reference_iff_engine, core_steps]
  cases permitted with
  | false => simp
  | true =>
      simp only [↓reduceIte, List.mem_flatMap, true_and]
      constructor
      · rintro ⟨⟨value, index⟩, member, outcome⟩
        by_cases chosen : value = token "A"
        · exact ⟨value, index, member, chosen, by simpa only [chosen, ↓reduceIte,
            List.mem_singleton] using outcome⟩
        · simp [chosen] at outcome
      · rintro ⟨value, index, member, chosen, endpoint⟩
        exact ⟨(value, index), member, by simp [chosen, endpoint]⟩

theorem selected_index {items : List Pattern} {value : Pattern} {index : Nat}
    (member : (value, index) ∈ items.zipIdx) :
    ∃ within : index < items.length, items[index] = value := by
  obtain ⟨selected, within, pair⟩ := List.exists_mem_zipIdx'.mp ⟨_, member, rfl⟩
  have same : selected = index := (Prod.mk.inj pair).2.symm
  subst selected
  exact ⟨within, (Prod.mk.inj pair).1.symm⟩


theorem root_firing_iff_selection (permitted : Bool) (items : List Pattern) (target : Pattern)
    (sourceTyped : OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Workflow") (workflow items)) :
    (∃ trace captured completed history,
      GeneralPremise.RootFiring (environment permitted) [] (.base "Workflow") (workflow items)
        0 trace captured completed history target) ↔
      permitted = true ∧ SelectedResult items target := by
  have places := Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.SearchAgreement.workflow_items_place sourceTyped
  constructor
  · rintro ⟨trace, captured, completed, history, fired⟩
    cases fired with
    | @fire _ _ _ _ _ actualRule actualSpec _ _ _ _ declared specified admitted
        typed matching capturedTyped premises reduced targetTyped =>
        have ruleEq : actualRule = rule :=
          Option.some.inj (declared.symm.trans (selected_rule permitted))
        cases ruleEq
        have specEq : actualSpec = specification :=
          Option.some.inj (specified.symm.trans (selected_specification permitted))
        cases specEq
        obtain ⟨enabled, same, _⟩ := premises_permit_readout premises
        cases same
        have member : captured ∈ matchRuleAt rule specification 0 (workflow items) :=
          GeneralScopedMatch.matchRuleAt_iff.mpr matching.matching
        rw [scoped_matches items places] at member
        obtain ⟨⟨value, index⟩, indexed, selected⟩ := List.mem_flatMap.mp member
        dsimp only at selected
        by_cases chosen : value = token "A"
        · simp only [chosen, ↓reduceIte, List.mem_singleton] at selected
          have ordinaryReduced : reduct? rule specification 0 captured = some target := by
            simpa only [List.length_nil, ordinary_reduct] using reduced
          rw [selected] at ordinaryReduced
          have expected := rest_reduct (items.eraseIdx index)
            (marking_scope_of_places _ (places_erased index places))
          exact ⟨enabled, value, index, indexed, chosen,
            Option.some.inj (ordinaryReduced.symm.trans expected)⟩
        · simp [chosen] at selected
  · rintro ⟨enabled, value, index, indexed, chosen, endpoint⟩
    subst permitted
    subst target
    obtain ⟨within, selected⟩ := selected_index indexed
    have residualPlaces := places_erased index places
    have residualScope := marking_scope_of_places _ residualPlaces
    have matching := scoped_match_selected index within (selected.trans chosen) residualScope
    obtain ⟨trace, traced⟩ := GeneralScopedMatchMachine.matches_trace matching
    have capturedTyped := rest_assignment_typed true (items.eraseIdx index) residualPlaces
    have targetPlaces : ∀ item ∈ token "B" :: items.eraseIdx index,
        item = token "A" ∨ item = token "B" := by
      intro item member
      rcases List.mem_cons.mp member with rfl | later
      · exact .inr rfl
      · exact residualPlaces item later
    have reduced : reductWith? (ScopedReflectiveExecution.binderOperation
        (environment true).reflection rule) rule specification 0
        (restAssignment (items.eraseIdx index)) =
        some (workflow (token "B" :: items.eraseIdx index)) := by
      simpa only [ordinary_reduct] using rest_reduct (items.eraseIdx index) residualScope
    refine ⟨trace, restAssignment (items.eraseIdx index), restAssignment (items.eraseIdx index),
      [.query 0 0 0 []], ?_⟩
    exact .fire (selected_rule true) (selected_specification true) rule_admitted sourceTyped
      traced capturedTyped (premises_permit rfl capturedTyped) reduced
      (workflow_open_of_places true _ targetPlaces)

theorem typed_core_reference_iff_root_firing (permitted : Bool) (items : List Pattern)
    (target : Pattern)
    (sourceTyped : OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Workflow") (workflow items)) :
    ReferenceStep.Step (relations permitted) (environment permitted).language
      (workflow items) target ↔
      ∃ trace captured completed history,
        GeneralPremise.RootFiring (environment permitted) [] (.base "Workflow") (workflow items)
          0 trace captured completed history target := by
  rw [environment_language]
  exact (reference_iff_selection permitted items target).trans
    (root_firing_iff_selection permitted items target sourceTyped).symm

theorem authored_reference_iff_root_firing (permitted : Bool) (items : List Pattern)
    (target : Pattern)
    (sourceTyped : OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Workflow") (lower (wrappedWorkflow items))) :
    (∃ authoredTarget, ReferenceStep.Step (relations permitted) authored
      (wrappedWorkflow items) authoredTarget ∧ lower authoredTarget = target) ↔
      ∃ trace captured completed history,
        GeneralPremise.RootFiring (environment permitted) [] (.base "Workflow")
          (lower (wrappedWorkflow items)) 0 trace captured completed history target := by
  rw [authored_reference_iff_core_reference]
  rw [lowers_workflow] at sourceTyped ⊢
  rw [← environment_language permitted]
  exact typed_core_reference_iff_root_firing permitted (items.map lower) target sourceTyped


theorem authored_box_reference_iff_contextual_instance (permitted : Bool)
    (items : List Pattern) (target : Pattern)
    (sourceTyped : OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Workflow") (lower (wrappedWorkflow items))) :
    (∃ authoredTarget, ReferenceStep.Step (relations permitted) authored
      (wrappedWorkflow items) authoredTarget ∧ lower (.apply "Box" [authoredTarget]) = target) ↔
      ∃ (site : TypedContextualEquationExecution.Site (environment permitted).language
          (environment permitted).free [] (.base "Workspace") [BoxAgreement.boxContext]
          (boxed (items.map lower)))
        (receipt : TypedContextualEquationExecution.Receipt),
        ContextualAuthoredEquationExecution.ContextualInstance (relations permitted)
          (environment permitted).language (environment permitted).free [] (.base "Workspace")
          [BoxAgreement.boxContext] (boxed (items.map lower)) 0 0 rule site receipt ∧
        receipt.target = target := by
  constructor
  · rintro ⟨authoredTarget, stepped, endpoint⟩
    have root := (authored_reference_iff_root_firing permitted items
      (lower authoredTarget) sourceTyped).mp ⟨authoredTarget, stepped, rfl⟩
    rw [lowers_workflow] at root
    obtain ⟨site, receipt, valid, _, outerEq⟩ :=
      (BoxAgreement.guarded_root_iff_exists_box_contextual_instance permitted
        (items.map lower) (lower authoredTarget)).mp root
    refine ⟨site, receipt, valid, ?_⟩
    calc
      receipt.target = BoxAgreement.boxContext.fill (lower authoredTarget) := outerEq
      _ = lower (.apply "Box" [authoredTarget]) := (lower_box_context authoredTarget).symm
      _ = target := endpoint
  · rintro ⟨site, receipt, valid, endpoint⟩
    obtain ⟨trace, history, root⟩ := conditional_instance_to_guarded_root
      (BoxAgreement.any_boxed_instance_to_atomic valid)
    have lowerRoot : GeneralPremise.RootFiring (environment permitted) [] (.base "Workflow")
        (lower (wrappedWorkflow items)) 0 trace receipt.atomic.captured receipt.atomic.completed
        history receipt.atomic.target := by
      simpa only [lowers_workflow] using root
    obtain ⟨authoredTarget, stepped, lowerEq⟩ :=
      (authored_reference_iff_root_firing permitted items receipt.atomic.target sourceTyped).mpr
        ⟨trace, receipt.atomic.captured, receipt.atomic.completed, history, lowerRoot⟩
    refine ⟨authoredTarget, stepped, ?_⟩
    calc
      lower (.apply "Box" [authoredTarget]) =
          BoxAgreement.boxContext.fill (lower authoredTarget) := lower_box_context authoredTarget
      _ = BoxAgreement.boxContext.fill receipt.atomic.target := congrArg _ lowerEq
      _ = receipt.target := (BoxAgreement.any_boxed_instance_readout valid).2.2.2.2.2.symm
      _ = target := endpoint

theorem typed_permitted_control :
    ReferenceStep.Step (relations true) (environment true).language
      (workflow [token "A", token "A", token "B"])
      (workflow [token "B", token "A", token "B"]) := by
  have sourceTyped := workflow_open_of_places true [token "A", token "A", token "B"] (by
    intro item member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp)
  apply (typed_core_reference_iff_root_firing true _ _ sourceTyped).mpr
  obtain ⟨trace, history, fired⟩ := RootAgreement.permitted_sample_root
  exact ⟨trace, RootAgreement.sampleCaptured, RootAgreement.sampleCaptured, history, fired⟩

theorem typed_refused_control (items : List Pattern)
    (sourceTyped : OpenPatternWellSorted (environment false).language (environment false).free []
      (.base "Workflow") (workflow items)) :
    ∀ target, ¬ ReferenceStep.Step (relations false) (environment false).language
      (workflow items) target := by
  intro target stepped
  exact RootAgreement.refused_root items target
    ((typed_core_reference_iff_root_firing false items target sourceTyped).mp stepped)


theorem authored_reference_iff_search_publication (permitted : Bool) (depth : Nat)
    (items : List Pattern) (target : Pattern)
    (sourceTyped : OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Workflow") (lower (wrappedWorkflow items))) :
    (∃ authoredTarget, ReferenceStep.Step (relations permitted) authored
      (wrappedWorkflow items) authoredTarget ∧ Same target (lower (.apply "Box" [authoredTarget]))) ↔
      ∃ work receipt, receipt ∈
        (CollectionOccurrenceSearch.search (plan permitted) [] (.base "Workspace") depth).publication
          ((CollectionOccurrenceSearch.search (plan permitted) [] (.base "Workspace") depth).run
            (lower (wrappedBox items)) work) ∧ Same target receipt.target := by
  rw [lowers_box, Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.SearchAgreement.search_iff_box_contextual_instance]
  constructor
  · rintro ⟨authoredTarget, stepped, observed⟩
    obtain ⟨site, receipt, valid, endpoint⟩ :=
      (authored_box_reference_iff_contextual_instance permitted items
        (lower (.apply "Box" [authoredTarget])) sourceTyped).mp ⟨authoredTarget, stepped, rfl⟩
    refine ⟨site, receipt, valid, ?_⟩
    rw [endpoint]
    exact observed
  · rintro ⟨site, receipt, valid, observed⟩
    obtain ⟨authoredTarget, stepped, endpoint⟩ :=
      (authored_box_reference_iff_contextual_instance permitted items receipt.target sourceTyped).mpr
        ⟨site, receipt, valid, rfl⟩
    refine ⟨authoredTarget, stepped, ?_⟩
    rw [endpoint]
    exact observed

theorem authored_permitted_search_control (depth : Nat) :
    ∃ work receipt, receipt ∈
      (CollectionOccurrenceSearch.search (plan true) [] (.base "Workspace") depth).publication
        ((CollectionOccurrenceSearch.search (plan true) [] (.base "Workspace") depth).run
          (lower (wrappedBox [token "A", token "A", token "B"])) work) ∧
      Same (lower (wrappedBox [token "B", token "A", token "B"])) receipt.target := by
  have sourceTyped : OpenPatternWellSorted (environment true).language (environment true).free []
      (.base "Workflow") (lower (wrappedWorkflow [token "A", token "A", token "B"])) := by
    rw [lowers_workflow]
    simp only [List.map_cons, List.map_nil, lower_token]
    apply workflow_open_of_places
    intro item member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp
  apply (authored_reference_iff_search_publication true depth _ _ sourceTyped).mp
  refine ⟨wrappedWorkflow [token "B", token "A", token "B"], ?_, rfl⟩
  apply (authored_reference_iff_engine true _ _).mpr
  rw [permitted_equal_tokens]
  exact .head _

theorem authored_refused_search_control (depth : Nat) (items : List Pattern)
    (sourceTyped : OpenPatternWellSorted (environment false).language (environment false).free []
      (.base "Workflow") (lower (wrappedWorkflow items))) :
    ¬ ∃ work receipt, receipt ∈
      (CollectionOccurrenceSearch.search (plan false) [] (.base "Workspace") depth).publication
        ((CollectionOccurrenceSearch.search (plan false) [] (.base "Workspace") depth).run
          (lower (wrappedBox items)) work) := by
  rintro ⟨work, receipt, published⟩
  obtain ⟨authoredTarget, stepped, _⟩ :=
    (authored_reference_iff_search_publication false depth items receipt.target sourceTyped).mpr
      ⟨work, receipt, published, rfl⟩
  have member := (authored_reference_iff_engine false _ _).mp stepped
  rw [refused_source] at member
  exact List.not_mem_nil member

#print axioms source_rule_selected
#print axioms bare_labels
#print axioms source_rule_left
#print axioms source_rule_right
#print axioms source_rule_premises
#print axioms core_rule_left
#print axioms core_rule_right
#print axioms core_rule_premises
#print axioms lowers_marking
#print axioms lowers_workflow
#print axioms lowers_box
#print axioms match_unary
#print axioms matches_exact
#print axioms origin_indices_exact
#print axioms lower_token
#print axioms lowered_reduct
#print axioms core_reduct
#print axioms instantiated_square
#print axioms match_token
#print axioms source_matches
#print axioms source_reduct
#print axioms permit_query
#print axioms permit_premises
#print axioms guarded_application
#print axioms source_steps
#print axioms core_steps
#print axioms lower_token_iff
#print axioms guarded_execution_square
#print axioms actual_rule_reduction
#print axioms actual_left_reduction
#print axioms actual_right_reduction
#print axioms rule_origin_retained
#print axioms no_equations_discarded
#print axioms nullary_premises_iff
#print axioms reference_iff_engine
#print axioms authored_reference_iff_engine
#print axioms core_reference_iff_engine
#print axioms authored_reference_iff_core_reference
#print axioms refused_source
#print axioms permitted_equal_tokens
#print axioms wrong_wrapper_refused
#print axioms malformed_wrapper_retained
#print axioms malformed_wrapper_refused
#print axioms wrong_kind_declaration_assigns_carrier
#print axioms wrong_kind_separates_raw_presentations
#print axioms raw_wrappers_are_not_core_inputs
#print axioms lowered_wrong_kind_passes_core_check
#print axioms lower_box_context
#print axioms boxed_execution_square
#print axioms environment_language
#print axioms recovery_identity
#print axioms occurrence_identity
#print axioms recover_root
#print axioms instantiate_root
#print axioms rest_capture
#print axioms scoped_match_selected
#print axioms places_properties
#print axioms places_erased
#print axioms marking_scope_of_places
#print axioms token_a_open
#print axioms token_b_open
#print axioms marking_declaration
#print axioms flow_declaration
#print axioms marking_decl_shape
#print axioms marking_decl_category
#print axioms flow_decl_parameters
#print axioms flow_decl_label
#print axioms flow_decl_category
#print axioms flow_decl_bare
#print axioms marking_typed_of_places
#print axioms workflow_open_of_places
#print axioms atom_scoped_match
#print axioms scoped_matches
#print axioms rest_assignment_typed
#print axioms rest_reduct
#print axioms reference_iff_selection
#print axioms selected_index
#print axioms root_firing_iff_selection
#print axioms typed_core_reference_iff_root_firing
#print axioms authored_reference_iff_root_firing
#print axioms authored_box_reference_iff_contextual_instance
#print axioms typed_permitted_control
#print axioms typed_refused_control
#print axioms authored_reference_iff_search_publication
#print axioms authored_permitted_search_control
#print axioms authored_refused_search_control

end Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.AuthoredAgreement

/-! The actual oriented-process module supplies this conditional sum rule. The
controls use its lowered language and canonical collection matching. They
check the child-rule history, failed child search, insufficient premise depth,
canonical observations and exact retention across resumption. -/

namespace Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.ActualSum

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise RuleBinding ScopedRuleMatching
open StructuralDescent.Scheduled

def language : LanguageDef :=
  Mettapedia.Languages.ProcessCalculi.OrientedRho.core.getD (LanguageDef.empty "")

def environment : Environment where
  language := language
  free := fun _ => none
  provider := { signatures := [], rows := [] }
  specifications := language.rewrites.zipIdx.map fun (rule, index) =>
    (index, GeneralRuleBindingInference.inferredSpec rule)

def chaos : Pattern := .apply "PChaos" []
def zero : Pattern := .apply "PZero" []
def sum (items : List Pattern) : Pattern :=
  .collection .hashSet items none

def goal (depth : Nat) (element : Pattern) : Goal :=
  .root depth [] (.base "Proc") (sum [element]) 1

def result (depth : Nat) (element : Pattern) (fuel : Nat) :
    State environment (goal depth element) RecursiveCollectionHandoff.canonicalMatchingExecution :=
  run environment (goal depth element) fuel
    (start environment (goal depth element) RecursiveCollectionHandoff.canonicalMatchingExecution)

#guard (language.rewrites[1]?).map (fun rule => (rule.name, rule.premises)) ==
  some ("RSum", [.congruence (.fvar "S") (.fvar "T")])

def targets {depth : Nat} {element : Pattern}
    (search : State environment (goal depth element)
      RecursiveCollectionHandoff.canonicalMatchingExecution) : List Pattern :=
  search.answers.map fun answer =>
    match answer with
    | .root _ _ _ _ target _ => CanonicalBags.canon target

def usedChild {Choice : Type} (history : List (Event Choice)) (index : Nat) : Bool :=
  history.any fun event =>
    match event with
    | .child _ _ actual .. => actual == index
    | _ => false

#guard ((result 2 chaos 500).answers.length, (result 2 chaos 500).agenda.length,
  (result 2 chaos 500).unresolved.length) == (2, 0, 0)
#guard (targets (result 2 chaos 500)).eraseDups == [sum [chaos]]
#guard (result 2 chaos 500).answers.all (fun answer =>
  match answer with
  | .root _ _ _ history _ _ => usedChild history 2)
#guard ((result 2 zero 500).answers.length, (result 2 zero 500).agenda.length,
  (result 2 zero 500).unresolved.length) == (0, 0, 0)
#guard (result 1 chaos 500).answers.isEmpty && !(result 1 chaos 500).unresolved.isEmpty
#guard !(targets (result 2 chaos 500)).contains (sum [zero])

theorem resumed_receipt_account :
    run environment (goal 2 chaos) 200
      (run environment (goal 2 chaos) 300
        (start environment (goal 2 chaos) RecursiveCollectionHandoff.canonicalMatchingExecution)) =
      result 2 chaos 500 :=
  (run_add environment (goal 2 chaos) 300 200
    (start environment (goal 2 chaos) RecursiveCollectionHandoff.canonicalMatchingExecution)).symm

#print axioms resumed_receipt_account

end Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.ActualSum


namespace Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.ModuloAgreement
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching CanonicalBags DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics
open RootAgreement BoxAgreement SearchAgreement
set_option maxHeartbeats 1600000

abbrev base (permitted : Bool) : ContextualStep.BasePremiseEvaluator :=
  ContextualStep.engineBasePremises (relations permitted)

theorem core_has_no_equations (permitted : Bool) : (environment permitted).language.equations = [] := by
  cases permitted <;> cbv
theorem core_has_no_set_or_algebra (permitted : Bool) :
    (environment permitted).language.usesCollection .hashSet = false ∧
      (environment permitted).language.hasAlgebraDeclarations = false := by
  cases permitted <;> cbv

private theorem canon_fill (context : OneHoleContext) {first second : Pattern}
    (same : Same first second) : Same (context.fill first) (context.fill second) := by
  induction context with
  | hole => exact same
  | apply label before inner after ih =>
      simpa only [Same,OneHoleContext.fill,canon_apply,List.map_append,List.map_cons] using
        congrArg (fun focus => Pattern.apply label (before.map canon ++ focus :: after.map canon)) ih
  | lambda binder inner ih => simpa only [Same,OneHoleContext.fill,canon] using congrArg (Pattern.lambda binder) ih
  | multiLambda arity binders inner ih =>
      simpa only [Same,OneHoleContext.fill,canon] using congrArg (Pattern.multiLambda arity binders) ih
  | substBody inner replacement ih =>
      simpa only [Same,OneHoleContext.fill,canon] using congrArg (fun focus => Pattern.subst focus (canon replacement)) ih
  | substReplacement body inner ih =>
      simpa only [Same,OneHoleContext.fill,canon] using congrArg (Pattern.subst (canon body)) ih
  | collection kind before inner after rest ih =>
      simp only [Same,OneHoleContext.fill,canon_collection,List.map_append,List.map_cons]
      rw [show canon (inner.fill first) = canon (inner.fill second) from ih]

theorem equationEquiv_same {permitted : Bool} {first second : Pattern}
    (related : EquationEquiv (base permitted) (environment permitted).language first second) :
    Same first second := by
  apply equationEquiv_invariant canon (fun context _ _ same => canon_fill context same) _ related
  intro source target generator
  rcases generator with authored | derived
  · obtain ⟨fuel,authored⟩ := authored
    cases authored with
    | forward member _ _ _ => rw [core_has_no_equations] at member; cases member
    | reverse member _ _ _ => rw [core_has_no_equations] at member; cases member
    | declared member _ _ => rw [core_has_no_equations] at member; cases member
  · obtain ⟨noSets,noAlgebra⟩ := core_has_no_set_or_algebra permitted
    cases derived with
    | bagPerm declaration sorted permutation =>
        exact (BagStep.permute (by rfl) permutation).canon_eq
    | setPerm declaration kindTyped _ =>
        have impossible := usesCollection_eq_true_of_collectionTypedAt declaration kindTyped
        rw [noSets] at impossible
        cases impossible
    | setDedup declaration kindTyped =>
        have impossible := usesCollection_eq_true_of_collectionTypedAt declaration kindTyped
        rw [noSets] at impossible
        cases impossible
    | flatten declaration _ _ => exact (no_algebraRule_of_hasAlgebraDeclarations_eq_false noAlgebra declaration).elim
    | singleton declaration _ _ => exact (no_algebraRule_of_hasAlgebraDeclarations_eq_false noAlgebra declaration).elim
    | unitElim declaration _ _ => exact (no_algebraRule_of_hasAlgebraDeclarations_eq_false noAlgebra declaration).elim
    | emptyUnit declaration _ _ => exact (no_algebraRule_of_hasAlgebraDeclarations_eq_false noAlgebra declaration).elim

theorem workflow_same_shape {items : List Pattern} {other : Pattern}
    (same : Same (workflow items) other) :
    ∃ others, other = workflow others ∧ Same (workflow items) (workflow others) := by
  obtain ⟨arguments,otherEq,argumentSame⟩ := same_apply same
  subst other
  cases arguments with
  | nil => cases argumentSame
  | cons markingOther after =>
      have afterNil : after = [] := List.map_eq_nil_iff.mp (List.cons.inj argumentSame).2.symm
      subst after
      have markingSame : Same (marking items) markingOther := (List.cons.inj argumentSame).1
      obtain ⟨others,markingEq,_⟩ := same_collection markingSame
      subst markingOther
      exact ⟨others,rfl,same⟩

theorem workflow_canon (items : List Pattern)
    (places : ∀ item ∈ items, item = token "A" ∨ item = token "B") :
    canon (workflow items) = workflow (arrange .hashBag items) := by
  have pointwise : items.map canon = items := by
    exact (List.map_congr_left (fun item member => by
      rcases places item member with rfl | rfl <;> simp [token,canon])).trans (List.map_id items)
  simp only [workflow,marking,canon_apply,List.map_cons,List.map_nil,canon_collection,pointwise]

theorem workflow_equiv_canon {permitted : Bool} {items : List Pattern}
    (typed : OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Workflow") (workflow items)) :
    EquationEquiv (base permitted) (environment permitted).language (workflow items) (canon (workflow items)) := by
  have places := workflow_items_place typed
  rw [workflow_canon items places]
  have sorted : SortedAt (environment permitted).language (marking items) "Marking" :=
    ⟨(environment permitted).free,[],AuthoredAgreement.marking_typed_of_places permitted items places⟩
  have selected := DerivedInstance.bagPerm_of_sorted sorted
    (PatternLexOrder.sortLex_perm items).symm
  exact .rel _ _ (.inContext (.apply "Flow" [] .hole []) (.inr selected))

theorem workflow_equiv_iff_same {permitted : Bool} {items : List Pattern} {other : Pattern}
    (typed : OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Workflow") (workflow items)) :
    EquationEquiv (base permitted) (environment permitted).language (workflow items) other ↔
      Same (workflow items) other := by
  refine ⟨equationEquiv_same,?_⟩
  intro same
  obtain ⟨others,rfl,_⟩ := workflow_same_shape same
  have otherTyped := openPatternWellSorted_of_eqvGen ((same_iff _ _).mp same) typed
  exact .trans _ _ _ (workflow_equiv_canon typed)
    (same ▸ (workflow_equiv_canon otherTyped).symm)

theorem contextual_iff_reference (permitted : Bool) (source target : Pattern) :
    ContextualStep.Step (base permitted) (environment permitted).language source target ↔
      ReferenceStep.Step (relations permitted) (environment permitted).language source target := by
  have selected : (environment permitted).language.rewrites = [rule] := by cases permitted <;> cbv
  have noncontextual : ∀ actual ∈ (environment permitted).language.rewrites,
      ContextualStep.NoncontextualPremises actual.premises := by
    intro actual member
    rw [selected] at member
    have same := List.mem_singleton.mp member
    subst actual
    rw [rule_premises]
    exact .relationQuery .nil
  rw [ContextualStep.step_iff_rootStep_of_noncontextualRules noncontextual,
    AuthoredAgreement.environment_language,AuthoredAgreement.core_reference_iff_engine]
  simp only [ContextualStep.RootStep,Engine.rewriteStepWithPremisesUsing,Engine.applyRuleWithPremisesUsing,
    List.mem_flatMap,List.mem_map]


/-- The actual declared root step modulo bag equations agrees with a typed
root firing at the original source, up to intrinsic bag presentation. -/
theorem stepModulo_iff_root_firing (permitted : Bool) (items : List Pattern) (target : Pattern)
    (sourceTyped : OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Workflow") (workflow items)) :
    StepModuloEquations (base permitted) (environment permitted).language (workflow items) target ↔
      ∃ trace captured completed history output,
        GeneralPremise.RootFiring (environment permitted) [] (.base "Workflow") (workflow items) 0
          trace captured completed history output ∧ Same target output := by
  constructor
  · rintro ⟨redex,contractum,before,fired,after⟩
    have sourceSame := equationEquiv_same before
    obtain ⟨others,redexEq,_⟩ := workflow_same_shape sourceSame
    subst redex
    have representativeTyped := openPatternWellSorted_of_eqvGen ((same_iff _ _).mp sourceSame) sourceTyped
    obtain ⟨trace,captured,completed,history,rooted⟩ :=
      (AuthoredAgreement.typed_core_reference_iff_root_firing permitted others contractum representativeTyped).mp
        ((contextual_iff_reference permitted _ _).mp fired)
    obtain ⟨trace',assignment,output,transported,targetSame⟩ :=
      guarded_root_same_source sourceSame.symm rooted
    exact ⟨trace',assignment,assignment,history,output,transported,
      (equationEquiv_same after).symm.trans targetSame⟩
  · rintro ⟨trace,captured,completed,history,output,rooted,same⟩
    have reference :=
      (AuthoredAgreement.typed_core_reference_iff_root_firing permitted items output sourceTyped).mpr
        ⟨trace,captured,completed,history,rooted⟩
    have outputTyped : OpenPatternWellSorted (environment permitted).language (environment permitted).free []
        (.base "Workflow") output := by cases rooted; assumption
    have selected := (AuthoredAgreement.reference_iff_selection permitted items output).mp
      (by simpa only [AuthoredAgreement.environment_language] using reference)
    obtain ⟨value,index,member,chosen,outputEq⟩ := selected.2
    have after : EquationEquiv (base permitted) (environment permitted).language output target := by
      rw [outputEq] at outputTyped ⊢
      exact (workflow_equiv_iff_same outputTyped).mpr (outputEq ▸ same.symm)
    exact ⟨workflow items,output,.refl _,(contextual_iff_reference permitted _ _).mpr reference,after⟩

/-- Every actual rule receipt in a closed workflow fires at its root. -/
theorem root_receipt_site {permitted : Bool} {items : List Pattern} {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid (plan permitted) [] (.base "Workflow") (workflow items)) :
    receipt.job.ordinal = 0 ∧ receipt.job.site.context = .hole ∧
      receipt.job.site.focus = workflow items ∧ receipt.job.site.focusBound = [] ∧
      receipt.job.site.focusType = .base "Workflow" := by
  have position := List.mk_mem_zipIdx_iff_getElem?.mp valid.1.1
  have within := (List.getElem?_eq_some_iff.mp position).1
  have oneRule : (plan permitted).rules.length = 1 := by cases permitted <;> cbv
  have ordinal : receipt.job.ordinal = 0 := by rw [oneRule] at within; omega
  have sourceTyped := GeneralRuleReceiptSource.primitive_source_sorted valid
  have places := workflow_items_place sourceTyped
  have flow : ∃ arguments, receipt.job.site.focus = .apply "Flow" arguments := by
    have firing := valid.2.1
    rw [ordinal] at firing
    cases firing with
    | @fire _ _ _ _ _ actualRule actualSpec _ _ _ _ declared _ _ _ matched _ _ _ _ =>
      have ruleEq : actualRule = rule := Option.some.inj (declared.symm.trans (selected_rule permitted))
      subst actualRule
      have matching := matched.matching
      rw [SearchAgreement.rule_left] at matching
      generalize focusEq : receipt.job.site.focus = focus at matching ⊢
      cases matching with
      | constructor arguments => exact ⟨_,rfl⟩
  obtain ⟨arguments,focusShape⟩ := flow
  have zipperEq := valid.1.2.source_eq
  rw [focusShape] at zipperEq
  obtain ⟨contextEq,localEq⟩ := SearchAgreement.flow_focus_in_workflow receipt.job.site.context arguments places zipperEq
  have focusEq := focusShape.trans localEq
  have selected := valid.1.2.typedAt
  rw [contextEq] at selected
  have focusIndices := selected.hole_indices
  exact ⟨ordinal,contextEq,focusEq,focusIndices.1,focusIndices.2⟩

theorem root_firing_to_receipt {permitted : Bool} {items : List Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List GeneralPremise.Event} {target : Pattern}
    (rooted : GeneralPremise.RootFiring (environment permitted) [] (.base "Workflow") (workflow items) 0
      trace captured completed history target) :
    ∃ receipt : GeneralRuleJobs.Receipt,
      receipt.Valid (plan permitted) [] (.base "Workflow") (workflow items) ∧ receipt.target = target := by
  have sourceTyped : OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Workflow") (workflow items) := by cases rooted; assumption
  have targetTyped : OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Workflow") target := by cases rooted; assumption
  let declaration := (plan permitted).rules[0]'(by cases permitted <;> cbv)
  have declared : (plan permitted).rules[0]? = some declaration :=
    List.getElem?_eq_getElem (by cases permitted <;> cbv)
  let job : GeneralRuleJobs.Job :=
    ⟨0,declaration,GeneralTypedSites.SiteData.here [] (.base "Workflow") (workflow items)⟩
  have licensed : job.Valid (plan permitted) [] (.base "Workflow") (workflow items) :=
    ⟨List.mk_mem_zipIdx_iff_getElem?.mpr declared,.here rfl sourceTyped.2.2.1 sourceTyped.1⟩
  let receipt : GeneralRuleJobs.Receipt := ⟨job,trace,captured,completed,history,target,target⟩
  refine ⟨receipt,?_,rfl⟩
  refine ⟨licensed,?_,rfl,rfl,targetTyped⟩
  simpa only [GeneralPlanEnvironment.environmentWith_empty,receipt,job,GeneralTypedSites.SiteData.here] using rooted

theorem modelEquiv_of_same_workflow (permitted : Bool) {left right : Pattern} (same : Same left right) :
    Complete.Presented.ModelEquiv (plan permitted) [] (.base "Workflow") left right := by
  have first := Complete.Presented.canon_equiv (plan permitted) [] (.base "Workflow") left
  have second := Complete.Presented.canon_equiv (plan permitted) [] (.base "Workflow") right
  change canon left = canon right at same
  rw [same] at first
  exact .trans _ _ _ first (.symm _ _ second)

theorem presented_root_iff_firing (permitted : Bool) (items : List Pattern) (target : Pattern) :
    (Complete.Presented.gslt (plan permitted) [] (.base "Workflow")).Step (workflow items) target ↔
      ∃ trace captured completed history output,
        GeneralPremise.RootFiring (environment permitted) [] (.base "Workflow") (workflow items) 0
          trace captured completed history output ∧ Same target output := by
  constructor
  · rintro ⟨representative,receipt,before,valid,after⟩
    have ready := (occurrenceCertificate permitted).requirements
    have sourceSame : Same (workflow items) representative := CollectionRootSearch.modelEquiv_canon
      (.base "Workflow") ready.noEquations ready.noLaws ready.noExtrusions before
    have afterSame : Same receipt.target target := CollectionRootSearch.modelEquiv_canon
      (.base "Workflow") ready.noEquations ready.noLaws ready.noExtrusions after
    obtain ⟨others,representativeEq,_⟩ := workflow_same_shape sourceSame
    subst representative
    obtain ⟨ordinal,contextEq,focusEq,boundEq,typeEq⟩ := root_receipt_site valid
    have firing : GeneralPremise.RootFiring (environment permitted) [] (.base "Workflow") (workflow others) 0
        receipt.matcherTrace receipt.captured receipt.completed receipt.premiseHistory receipt.localTarget := by
      simpa only [GeneralPlanEnvironment.environmentWith_empty,ordinal,focusEq,boundEq,typeEq] using valid.2.1
    obtain ⟨trace,assignment,output,transported,sameTarget⟩ := guarded_root_same_source sourceSame.symm firing
    refine ⟨trace,assignment,assignment,receipt.premiseHistory,output,transported,?_⟩
    have filled : receipt.target = receipt.localTarget := by
      rw [valid.2.2.2.1,contextEq]
      rfl
    exact afterSame.symm.trans (filled ▸ sameTarget)
  · rintro ⟨trace,captured,completed,history,output,rooted,same⟩
    obtain ⟨receipt,valid,targetEq⟩ := root_firing_to_receipt rooted
    exact ⟨workflow items,receipt,.refl _,valid,
      modelEquiv_of_same_workflow permitted (targetEq ▸ same.symm)⟩

/-- The existing retained Search realizes the independently declared root
step modulo equations, with the ordinary permit guard and bag multiplicity. -/
theorem stepModulo_iff_search_publication (permitted : Bool) (depth : Nat)
    (items : List Pattern) (target : Pattern)
    (sourceTyped : OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Workflow") (workflow items)) :
    StepModuloEquations (base permitted) (environment permitted).language (workflow items) target ↔
      ∃ work receipt, receipt ∈
        (CollectionOccurrenceSearch.search (plan permitted) [] (.base "Workflow") depth).publication
          ((CollectionOccurrenceSearch.search (plan permitted) [] (.base "Workflow") depth).run
            (workflow items) work) ∧ Same target receipt.target :=
  (stepModulo_iff_root_firing permitted items target sourceTyped).trans
    ((presented_root_iff_firing permitted items target).symm.trans
      (CollectionOccurrenceAdmission.source_exact (occurrenceCertificate permitted) [] (.base "Workflow")
        depth (workflow items) target))


theorem boxed_equiv_iff_same {permitted : Bool} {items : List Pattern} {other : Pattern}
    (typed : OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Workspace") (boxed items)) :
    EquationEquiv (base permitted) (environment permitted).language (boxed items) other ↔ Same (boxed items) other := by
  refine ⟨equationEquiv_same,?_⟩
  intro same
  obtain ⟨others,rfl,innerSame⟩ := boxed_same_shape same
  exact equationEquiv_fill boxContext
    ((workflow_equiv_iff_same (workflow_open_of_boxed typed)).mpr innerSame)

/-- Box is a permitted execution context, not an authored congruence rule in
this module. Root StepModulo therefore never fires on a boxed workflow. -/
theorem no_boxed_root_stepModulo (permitted : Bool) (items : List Pattern) (target : Pattern) :
    ¬ StepModuloEquations (base permitted) (environment permitted).language (boxed items) target := by
  rintro ⟨redex,contractum,before,fired,_⟩
  obtain ⟨others,redexEq,_⟩ := boxed_same_shape (equationEquiv_same before)
  subst redex
  apply ContextualStep.not_step_of_matchPatternForRule_eq_nil (source := boxed others) _ fired
  intro actual member
  have selected : (environment permitted).language.rewrites = [rule] := by cases permitted <;> cbv
  rw [selected] at member
  have same := List.mem_singleton.mp member
  subst actual
  have labels : (("Flow" : String) == "Box") = false := by decide
  simp only [ReflectiveCanonical.matchPatternForRule_eq_syntactic,SearchAgreement.rule_left,boxed,Match.matchPattern,
    labels,Bool.false_and,Bool.false_eq_true,if_false]

/-- Explicitly lifting the actual root StepModulo through the checked Box
context gives exactly the existing Box-enabled Search successor classes. -/
theorem lifted_root_stepModulo_iff_box_search (permitted : Bool) (depth : Nat)
    (items : List Pattern) (target : Pattern)
    (sourceTyped : OpenPatternWellSorted (environment permitted).language (environment permitted).free []
      (.base "Workflow") (workflow items)) :
    (∃ localTarget, StepModuloEquations (base permitted) (environment permitted).language
      (workflow items) localTarget ∧ Same target (boxContext.fill localTarget)) ↔
      ∃ work receipt, receipt ∈
        (CollectionOccurrenceSearch.search (plan permitted) [] (.base "Workspace") depth).publication
          ((CollectionOccurrenceSearch.search (plan permitted) [] (.base "Workspace") depth).run
            (boxed items) work) ∧ Same target receipt.target := by
  constructor
  · rintro ⟨localTarget,stepped,outerSame⟩
    obtain ⟨trace,captured,completed,history,output,rooted,localSame⟩ :=
      (stepModulo_iff_root_firing permitted items localTarget sourceTyped).mp stepped
    obtain ⟨site,receipt,valid,_,targetEq⟩ :=
      (guarded_root_iff_exists_box_contextual_instance permitted items output).mp
        ⟨trace,captured,completed,history,rooted⟩
    apply (search_iff_box_contextual_instance permitted depth items target).mpr
    refine ⟨site,receipt,valid,?_⟩
    rw [targetEq]
    exact outerSame.trans (same_box_fill localSame)
  · intro published
    obtain ⟨site,receipt,valid,outerSame⟩ :=
      (search_iff_box_contextual_instance permitted depth items target).mp published
    obtain ⟨trace,history,rooted⟩ := conditional_instance_to_guarded_root (any_boxed_instance_to_atomic valid)
    refine ⟨receipt.atomic.target,?_,?_⟩
    · exact (stepModulo_iff_root_firing permitted items receipt.atomic.target sourceTyped).mpr
        ⟨trace,receipt.atomic.captured,receipt.atomic.completed,history,receipt.atomic.target,rooted,rfl⟩
    · rw [← (any_boxed_instance_readout valid).2.2.2.2.2]
      exact outerSame

theorem permitted_sample_stepModulo :
    StepModuloEquations (base true) (environment true).language (workflow sampleItems) sampleTarget := by
  obtain ⟨trace,history,rooted⟩ := permitted_sample_root
  have sourceTyped : OpenPatternWellSorted (environment true).language (environment true).free []
      (.base "Workflow") (workflow sampleItems) := by cases rooted; assumption
  exact (stepModulo_iff_root_firing true sampleItems sampleTarget sourceTyped).mpr
    ⟨trace,sampleCaptured,sampleCaptured,history,sampleTarget,rooted,rfl⟩

theorem refused_stepModulo {items : List Pattern} {target : Pattern}
    (sourceTyped : OpenPatternWellSorted (environment false).language (environment false).free []
      (.base "Workflow") (workflow items)) :
    ¬ StepModuloEquations (base false) (environment false).language (workflow items) target := by
  intro stepped
  obtain ⟨trace,captured,completed,history,output,rooted,_⟩ :=
    (stepModulo_iff_root_firing false items target sourceTyped).mp stepped
  have impossible := guarded_root_requires_permit rooted
  cases impossible

theorem boxed_execution_is_explicit_context_lift (depth : Nat) :
    (∃ work receipt, receipt ∈
      (CollectionOccurrenceSearch.search (plan true) [] (.base "Workspace") depth).publication
        ((CollectionOccurrenceSearch.search (plan true) [] (.base "Workspace") depth).run
          (boxed sampleItems) work) ∧ Same (boxContext.fill sampleTarget) receipt.target) ∧
      ¬ StepModuloEquations (base true) (environment true).language (boxed sampleItems) (boxContext.fill sampleTarget) :=
  ⟨permitted_sample_search depth,no_boxed_root_stepModulo true sampleItems _⟩

#print axioms boxed_equiv_iff_same
#print axioms no_boxed_root_stepModulo
#print axioms lifted_root_stepModulo_iff_box_search
#print axioms permitted_sample_stepModulo
#print axioms refused_stepModulo
#print axioms boxed_execution_is_explicit_context_lift

#print axioms stepModulo_iff_root_firing
#print axioms root_receipt_site
#print axioms root_firing_to_receipt
#print axioms presented_root_iff_firing
#print axioms stepModulo_iff_search_publication

#print axioms equationEquiv_same
#print axioms workflow_equiv_canon
#print axioms workflow_equiv_iff_same
#print axioms contextual_iff_reference
end Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.ModuloAgreement

namespace Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.ActualSum

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Mettapedia.GSLT.LanguageDef.ModuleSource

@[local cbv_eval] private theorem source_origin_eq_fields (first second : Origin) :
    (first = second) = (first.inst = second.inst ∧ first.name = second.name) := by
  cases first
  cases second
  simp

@[local cbv_eval] private theorem source_label_eq_fields (first second : Label) :
    (first = second) = (first.1 = second.1 ∧ first.2 = second.2) := by
  cases first
  cases second
  simp

open Lean Meta in
local cbv_simproc cbv_eval sumSourceStringDecidable (String.decEq _ _) := fun e => do
  let_expr String.decEq first second := e | return .rfl
  let some firstValue := Sym.getStringValue? first | return .rfl
  let some secondValue := Sym.getStringValue? second | return .rfl
  let literalProof ← if firstValue == secondValue then mkEqRefl first
    else mkStringLitNeProof firstValue secondValue
  let decidableConstructor := if firstValue == secondValue then ``Decidable.isTrue else ``Decidable.isFalse
  let result ← mkAppM decidableConstructor #[literalProof]
  let result ← Sym.share result
  let proof ← mkAppM ``Subsingleton.elim #[e,result]
  return .step result proof

@[local cbv_eval] private theorem sum_constructor_refs_nullary (label : String) :
    Pattern.constructorRefs (.apply label []) = [(label,0)] := by
  simp only [Pattern.constructorRefs,Pattern.constructorRefsList]
  rfl





private theorem source_constructor_refs_regular (label : String) (arguments : List Pattern)
    (notZip : label ≠ "$zip") (notMap : label ≠ "$map") (notEval : label ≠ "$eval") :
    Pattern.constructorRefs (.apply label arguments) = (label,arguments.length) :: Pattern.constructorRefsList arguments := by
  simp only [Pattern.constructorRefs]
  split <;> simp_all

open Lean Meta in
local cbv_simproc cbv_eval sourceRegularConstructorRefs (Pattern.constructorRefs (.apply _ _)) := fun e => do
  let_expr Pattern.constructorRefs pattern := e | return .rfl
  let_expr Pattern.apply label arguments := pattern | return .rfl
  let some constructorName := Sym.getStringValue? label | return .rfl
  if constructorName == "$zip" || constructorName == "$map" || constructorName == "$eval" then return .rfl
  let notZip ← mkStringLitNeProof constructorName "$zip"
  let notMap ← mkStringLitNeProof constructorName "$map"
  let notEval ← mkStringLitNeProof constructorName "$eval"
  let proof ← mkAppM ``source_constructor_refs_regular #[label,arguments,notZip,notMap,notEval]
  let proofType ← inferType proof
  let_expr Eq _ _ result := proofType | return .rfl
  return .step (← Sym.share result) proof

attribute [local cbv_opaque] String.decEq

/-- The certificate reads the actual lowered sum rule. Its selected source
is the captured element S, not the residual set or a provider output. -/
theorem lowered_sum_source :
    (language.rewrites[1]?).map (fun rule => (rule.left,rule.premises)) =
      some (.collection .hashSet [.fvar "S"] (some "rest"),[.congruence (.fvar "S") (.fvar "T")]) := by
  cbv

theorem lowered_parallel_source :
    (language.rewrites[0]?).map (fun rule => (rule.left,rule.premises)) =
      some (.collection .hashBag [.fvar "S"] (some "rest"),[.congruence (.fvar "S") (.fvar "T")]) := by cbv

private theorem profile_rule_premises : language.rewrites.map (·.premises) =
    [[.congruence (.fvar "S") (.fvar "T")],[.congruence (.fvar "S") (.fvar "T")],[],[]] := by cbv


/-- The existing generic ordinal checker refuses this recursive source.
In particular RDiv is a later declaration than RSum. -/
theorem ordinal_stratification_refused : GeneralPremise.checkStepStratification language = false := by
  cbv

/-- The actual foundation compiler retains its stratification obligation.
No claim of overall compilation success is made by the native sum controls. -/
theorem compiled_stratification_obligation :
    GeneralExecutionAdmission.Obligation.childStratification ∈
      (GeneralExecutionAdmission.compile
        ⟨language,[],environment.provider⟩ {}).obligations := by
  have rejected : GeneralPremise.checkStepStratification
      (GeneralExecutionAdmission.executionLanguage ⟨language,[],environment.provider⟩ {}) = false := by cbv
  simp only [GeneralExecutionAdmission.compile,List.mem_append,rejected,Bool.false_eq_true,
    ite_false,List.mem_singleton,or_true,true_or]

/-- Structural descent is checked from the actual lowered LHS, occurrence
specification and child schema; this is independent of declaration order. -/
theorem sum_source_certificate :
    (language.rewrites[1]?).map (fun rule => StructuralDescent.checkSource rule
      (GeneralRuleBindingInference.inferredSpec rule) 0 0 0 (.fvar "S")) = some true := by
  cbv

/-- The ordinary structural source certificate is valid for every lowered
row, including the binder-bearing communication declaration. -/
theorem ordinary_structural_environment : StructuralDescent.checkEnvironment environment = true := by
  cbv

/-- Any actual ordinary capture and premise instantiation on the selected
sum row strictly decreases raw source nodes. The theorem is about exact raw
representatives, not size invariance across equations or canonical matching. -/
theorem ordinary_sum_child_smaller {rule : RewriteRule} {ambient : Nat}
    {captured assignment : Assignment} {parent child : Pattern}
    (declared : language.rewrites[1]? = some rule)
    (matched : GeneralScopedMatch.Matches rule (GeneralRuleBindingInference.inferredSpec rule)
      ambient .left [] 0 [] rule.left parent captured)
    (extension : GeneralScopedMatch.Extends captured assignment)
    (instantiated : instantiateAt? rule (GeneralRuleBindingInference.inferredSpec rule) ambient
      (.premise 0 0 0) [] 0 assignment (.fvar "S") = some child) :
    PatternTreeSize.nodes child < PatternTreeSize.nodes parent := by
  have checked : StructuralDescent.checkSource rule
      (GeneralRuleBindingInference.inferredSpec rule) 0 0 0 (.fvar "S") = true := by
    simpa only [declared,Option.map_some,Option.some.injEq] using sum_source_certificate
  exact StructuralDescent.actual_source_decreases checked matched extension instantiated

/-- The already-proved structural theorem supplies the per-state ordinary
source depth bound for every actual raw receipt. It is not automatically a
bound for the separate canonical collection interpretation. -/
theorem ordinary_source_depth_bound (source : Pattern) (bound : List TypeExpr) (type : TypeExpr)
    (answer : StructuralDescent.Execution.RootAnswer environment bound type source) :
    answer.requiredDepth ≤ PatternTreeSize.nodes source :=
  StructuralDescent.firing_depth_bound environment ordinary_structural_environment source bound type answer

/-- The existing shared ordinary scheduler covers every such receipt at its
proved source-size budget, retaining its full tuple of origins and histories. -/
theorem ordinary_complete_receipts (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (index : Nat) (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : Assignment)
    (history : List Event) (target : Pattern) :
    (∃ answer ∈ StructuralDescent.Scheduled.receipts
        (StructuralDescent.Scheduled.finishSource environment bound type source),
      answer.index = index ∧ answer.trace = trace ∧ answer.captured = captured ∧
      answer.completed = completed ∧ answer.history = history ∧ answer.target = target) ↔
    RootFiring environment bound type source index trace captured completed history target :=
  StructuralDescent.Scheduled.finishSource_occurrences environment ordinary_structural_environment
    bound type source index trace captured completed history target


#print axioms sum_constructor_refs_nullary
#print axioms source_origin_eq_fields
#print axioms source_label_eq_fields
#print axioms lowered_sum_source
#print axioms ordinal_stratification_refused
#print axioms compiled_stratification_obligation
#print axioms sum_source_certificate
#print axioms ordinary_structural_environment
#print axioms ordinary_sum_child_smaller
#print axioms ordinary_source_depth_bound
#print axioms ordinary_complete_receipts


/-- Singleton collapse is retained as an actual authored row of the core;
it is not an intrinsic CanonicalBags identification. -/
theorem actual_singleton_row :
    (language.equations[3]?).map (fun row => (row.left,row.right,row.premises,ReferenceStep.readsRaw row)) =
      some (.collection .hashSet [.fvar "P"] none,.fvar "P",[],true) := by cbv

/-- The existing independent reference equation judgment realizes the real
singleton row, with its exact raw matching and source substitution. -/
theorem actual_singleton_instance (value : Pattern) :
    ReferenceStep.AuthoredEquation Engine.RelationEnv.empty language (sum [value]) value := by
  obtain ⟨row,declared,shape⟩ := Option.map_eq_some_iff.mp actual_singleton_row
  simp only [Prod.mk.injEq] at shape
  obtain ⟨leftShape,rightShape,premisesShape,undeclared⟩ := shape
  let bindings : Match.Bindings := [("P",value)]
  have matched : bindings ∈ Match.matchPattern row.left (sum [value]) := by
    rw [leftShape]
    cbv
    exact List.mem_singleton_self _
  have premises : ReferenceStep.PremisesValid Engine.RelationEnv.empty language
      (ReferenceStep.captureSitesOf row.left row.premises) bindings row.premises [] bindings := by
    rw [premisesShape]
    exact .nil bindings
  have read : Match.applyBindingsScoped (ReferenceStep.captureSitesOf row.left row.premises) bindings 0 row.right =
      value := by
    rw [leftShape,rightShape,premisesShape]
    simp [Match.applyBindingsScoped,ReferenceStep.captureSitesOf,Match.captureDepth,Match.captureDepthList,
      bindings,Substitution.liftBVars_zero]
  have authoredInstance := ReferenceStep.AuthoredEquation.forward
    (List.mem_of_getElem? declared) undeclared matched premises
  simpa only [read] using authoredInstance

/-- This is the original full-syntax source equivalence, not a new quotient
or a raw equality between the wrapped and unwrapped presentations. -/
theorem actual_singleton_equivalent (value : Pattern) :
    ReferenceStep.Equivalent Engine.RelationEnv.empty language (sum [value]) value :=
  .rel _ _ (.inContext .hole (.inl (actual_singleton_instance value)))

/-- Both sides of the separator inhabit the actual closed process fibre,
so its size discrepancy is not caused by malformed or wrongly sorted data. -/
theorem actual_singleton_well_sorted :
    OpenPatternWellSorted language environment.free [] (.base "Proc") (sum [chaos]) ∧
      OpenPatternWellSorted language environment.free [] (.base "Proc") chaos :=
  ⟨checkOpenPatternWellSorted_sound (by cbv),checkOpenPatternWellSorted_sound (by cbv)⟩

/-- Raw source-node count is not invariant under the actual singleton row.
The ordinary subsource certificate therefore cannot simply be transported
along declared equations to an arbitrary normalized representative. -/
theorem actual_singleton_measure_separator :
    ReferenceStep.Equivalent Engine.RelationEnv.empty language (sum [chaos]) chaos ∧
      PatternTreeSize.nodes (sum [chaos]) = 2 ∧ PatternTreeSize.nodes chaos = 1 ∧
      ¬ CanonicalBags.Same (sum [chaos]) chaos := by
  refine ⟨actual_singleton_equivalent chaos,rfl,rfl,?_⟩
  intro same
  have sameKind := same
  change CanonicalBags.canon (sum [chaos]) = CanonicalBags.canon chaos at sameKind
  have impossible := congrArg (fun pattern => match pattern with
    | .collection .. => true
    | _ => false) sameKind
  simp only [sum,chaos,CanonicalBags.canon_collection,CanonicalBags.canon_apply] at impossible
  cases impossible

#print axioms actual_singleton_row
#print axioms actual_singleton_instance
#print axioms actual_singleton_equivalent
#print axioms actual_singleton_well_sorted
#print axioms actual_singleton_measure_separator

private theorem actual_sum_core :
    (language.rewrites[1]?).map (fun row => (row.left,row.right,row.premises)) =
      some (.collection .hashSet [.fvar "S"] (some "rest"),
        .collection .hashSet [.fvar "T"] (some "rest"),[.congruence (.fvar "S") (.fvar "T")]) := by cbv

private theorem actual_div_core :
    (language.rewrites[2]?).map (fun row => (row.left,row.right,row.premises)) =
      some (chaos,chaos,[]) := by cbv

private def expandedSumWitness : ReferenceStep.Witness :=
  .rule 1 [("rest",sum []),("S",chaos)]
    [.premiseStep (.rule 2 [] []) chaos [("T",chaos)]
      [("T",chaos),("rest",sum []),("S",chaos)]]

/-- An exact original reference witness uses the actual RSum row and its
later RDiv child on the singleton-expanded representative. -/
theorem actual_expanded_sum_reference :
    ReferenceStep.StepValid Engine.RelationEnv.empty language (sum [chaos])
      expandedSumWitness (sum [chaos]) := by
  obtain ⟨sumRule,sumDeclared,sumShape⟩ := Option.map_eq_some_iff.mp actual_sum_core
  obtain ⟨divRule,divDeclared,divShape⟩ := Option.map_eq_some_iff.mp actual_div_core
  simp only [Prod.mk.injEq] at sumShape divShape
  obtain ⟨sumLeft,sumRight,sumPremises⟩ := sumShape
  obtain ⟨divLeft,divRight,divPremises⟩ := divShape
  let initial : Match.Bindings := [("rest",sum []),("S",chaos)]
  let final : Match.Bindings := [("T",chaos),("rest",sum []),("S",chaos)]
  have sumSites : ReferenceStep.captureSites sumRule =
      ReferenceStep.captureSitesOf (.collection .hashSet [.fvar "S"] (some "rest"))
        [.congruence (.fvar "S") (.fvar "T")] := by
    simp only [ReferenceStep.captureSites,sumLeft,sumPremises]
  have divMatched : ([] : Match.Bindings) ∈ ReflectiveCanonical.matchPatternForRule language divRule chaos := by
    rw [ReflectiveCanonical.matchPatternForRule_eq_syntactic,divLeft]
    decide +kernel
  have divBodies : ReferenceStep.PremisesValid Engine.RelationEnv.empty language
      (ReferenceStep.captureSites divRule) [] divRule.premises [] [] := by
    rw [divPremises]
    exact .nil []
  have divTarget : Match.applyBindingsScoped (ReferenceStep.captureSites divRule) [] 0 divRule.right = chaos := by
    rw [divRight]
    rfl
  have child : ReferenceStep.StepValid Engine.RelationEnv.empty language chaos (.rule 2 [] []) chaos := by
    have root := ReferenceStep.StepValid.rule divDeclared divMatched divBodies
    simpa only [divTarget] using root
  have sourceRead : Match.applyBindingsScoped (ReferenceStep.captureSites sumRule) initial
      (ReferenceStep.stepDepth (ReferenceStep.captureSites sumRule) (.congruence (.fvar "S") (.fvar "T")))
      (.fvar "S") = chaos := by
    rw [sumSites]
    decide +kernel
  have childAt : ReferenceStep.StepValid Engine.RelationEnv.empty language
      (Match.applyBindingsScoped (ReferenceStep.captureSites sumRule) initial
        (ReferenceStep.stepDepth (ReferenceStep.captureSites sumRule) (.congruence (.fvar "S") (.fvar "T")))
        (.fvar "S")) (.rule 2 [] []) chaos := by
    rw [sourceRead]
    exact child
  have targetMatched : [("T",chaos)] ∈ Match.matchPattern (.fvar "T") chaos := by decide +kernel
  have merged : Match.mergeBindings initial [("T",chaos)] = some final := by decide +kernel
  have premise : ReferenceStep.PremiseValid Engine.RelationEnv.empty language (ReferenceStep.captureSites sumRule)
      initial (.congruence (.fvar "S") (.fvar "T"))
      (.premiseStep (.rule 2 [] []) chaos [("T",chaos)] final) final :=
    .step rfl childAt targetMatched merged
  have premises : ReferenceStep.PremisesValid Engine.RelationEnv.empty language
      (ReferenceStep.captureSites sumRule) initial sumRule.premises
      [.premiseStep (.rule 2 [] []) chaos [("T",chaos)] final] final := by
    rw [sumPremises]
    exact .cons premise (.nil final)
  have matched : initial ∈ ReflectiveCanonical.matchPatternForRule language sumRule (sum [chaos]) := by
    rw [ReflectiveCanonical.matchPatternForRule_eq_syntactic,sumLeft]
    decide +kernel
  have targetRead : Match.applyBindingsScoped (ReferenceStep.captureSites sumRule) final 0 sumRule.right =
      sum [chaos] := by
    rw [sumSites,sumRight]
    decide +kernel
  have root := ReferenceStep.StepValid.rule sumDeclared matched premises
  simpa only [targetRead,expandedSumWitness,initial,final] using root

/-- The actual authored singleton equation licenses this original source
step modulo equations at the unwrapped process representative. -/
theorem actual_quotient_sum_step :
    ReferenceStep.StepModulo Engine.RelationEnv.empty language chaos chaos :=
  ⟨sum [chaos],sum [chaos],(actual_singleton_equivalent chaos).symm,
    ⟨expandedSumWitness,actual_expanded_sum_reference⟩,actual_singleton_equivalent chaos⟩

/-- The installed canonical matcher does not recover that RSum origin at
bare chaos: intrinsic collection normalization preserves its constructor
head. This does not assert absence of the separate RDiv fact successor. -/
theorem canonical_bare_sum_origin_refused {trace : List EquationalScopedReceipts.Event}
    {captured completed : Assignment} {history : List (Event EquationalScopedReceipts.Event)} {target : Pattern}
    (fired : Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation
      environment [] (.base "Proc") chaos 1 trace captured completed history target) : False := by
  cases fired with
  | @fire _ _ _ _ _ rule spec _ _ _ _ declared _ _ _ matched _ _ _ _ =>
      have selected := lowered_sum_source
      change language.rewrites[1]? = some rule at declared
      rw [declared,Option.map_some,Option.some.injEq,Prod.mk.injEq] at selected
      have leftShape := selected.1
      change EquationalScopedReceipts.Matches literalBodyComparison rule spec 0 .left [] 0 []
        rule.left (CanonicalBags.canon chaos) trace captured at matched
      rw [leftShape] at matched
      simp only [chaos,CanonicalBags.canon_apply] at matched
      cases matched

#print axioms actual_sum_core
#print axioms actual_div_core
#print axioms actual_expanded_sum_reference
#print axioms actual_quotient_sum_step
#print axioms canonical_bare_sum_origin_refused



def proc : TypeExpr := .base "Proc"

/-- Only the operational fields are projected. The actual rule binding
packet remains in the original row and is not replaced by this readout. -/
theorem lowered_sum_fields :
    (language.rewrites[1]?).map (fun rule =>
      (rule.name,rule.typeContext,rule.left,rule.right,rule.premises)) =
      some ("RSum",[("S",proc),("rest",.collection .hashSet proc),("T",proc)],
        .collection .hashSet [.fvar "S"] (some "rest"),
        .collection .hashSet [.fvar "T"] (some "rest"),
        [.congruence (.fvar "S") (.fvar "T")]) := by cbv

#print axioms lowered_sum_fields

/-- The independent later child declaration is read at its original
ordinal. Its original binding packet remains in the selected row. -/
theorem lowered_div_fields :
    (language.rewrites[2]?).map (fun rule =>
      (rule.name,rule.typeContext,rule.left,rule.right,rule.premises)) =
      some ("RDiv",[],Pattern.apply "PChaos" [],Pattern.apply "PChaos" [],[]) := by cbv

#print axioms lowered_div_fields

def declaredCollectionRoles : List (String × CollType × TypeExpr) :=
  language.terms.filterMap fun rule =>
    match rule.bareParams with
    | [.simple _ (.collection kind element)] => some (rule.category,kind,element)
    | _ => none

/-- The complete actual grammar has exactly these two bare collection
roles. Other declaration fields remain in the original grammar records. -/
theorem declared_collection_roles : declaredCollectionRoles =
    [("Proc",.hashBag,proc),("Proc",.hashSet,proc)] := by cbv

#print axioms declared_collection_roles

/-- The actual chaos declaration supplies the empty argument spine of
the RDiv source and target. The complete source grammar remains unchanged. -/
theorem chaos_grammar_role :
    (language.terms.find? fun rule => rule.label == "PChaos").map
      (fun rule => (rule.label,rule.category,rule.params,rule.bareParams)) =
      some ("PChaos","Proc",[],[]) := by cbv

#print axioms chaos_grammar_role

/-- Core construction already retains its validator proof. Whether this
actual core has any declaration is established independently. -/
theorem language_valid : language.validate = [] := by
  unfold language Mettapedia.Languages.ProcessCalculi.OrientedRho.core
  generalize lowered : Mettapedia.Languages.ProcessCalculi.OrientedRho.language.toCore = result
  cases result with
  | error error => cbv
  | ok core =>
      change core.language.validate = []
      have checked := core.core
      simp only [CoreReduction.isCore,Bool.and_eq_true] at checked
      exact List.isEmpty_iff.mp checked.1.1

#print axioms language_valid
open Mettapedia.GSLT.LanguageDef.WellSorted
open _root_.Mettapedia.OSLF.MeTTaIL.Match GeneralFirstOrderProjection
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement QuantifiedReference

attribute [local cbv_opaque] language

/-- The selected actual binding packet is retained as a parameter. -/
def sumRuleWith (binding : Option RuleBindingSpec) : RewriteRule where
  «name» := "RSum"
  typeContext := [("S",proc),("rest",.collection .hashSet proc),("T",proc)]
  premises := [.congruence (.fvar "S") (.fvar "T")]
  left := .collection .hashSet [.fvar "S"] (some "rest")
  right := .collection .hashSet [.fvar "T"] (some "rest")
  bindings := binding

def divRuleWith (binding : Option RuleBindingSpec) : RewriteRule where
  «name» := "RDiv"
  typeContext := []
  premises := []
  left := chaos
  right := chaos
  bindings := binding

theorem actual_sum_template : ∃ binding,language.rewrites[1]? = some (sumRuleWith binding) := by
  obtain ⟨row,declared,shape⟩ := Option.map_eq_some_iff.mp lowered_sum_fields
  rcases row with ⟨ruleName,context,premises,left,right,binding⟩
  simp only [Prod.mk.injEq] at shape
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := shape
  exact ⟨binding,declared⟩

theorem actual_div_template : ∃ binding,language.rewrites[2]? = some (divRuleWith binding) := by
  obtain ⟨row,declared,shape⟩ := Option.map_eq_some_iff.mp lowered_div_fields
  rcases row with ⟨ruleName,context,premises,left,right,binding⟩
  simp only [Prod.mk.injEq] at shape
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := shape
  exact ⟨binding,declared⟩

/-- The original consumer enumerates each actual source row's specification
at the same ordinal. The lookup uses that real enumeration. -/
theorem specification_of_declared {index : Nat} {rule : RewriteRule}
    (declared : language.rewrites[index]? = some rule) :
    GeneralPremise.specification? environment index = some (GeneralRuleBindingInference.inferredSpec rule) := by
  have member : (rule,index) ∈ language.rewrites.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr declared
  have mapped : (index,GeneralRuleBindingInference.inferredSpec rule) ∈ environment.specifications :=
    List.mem_map.mpr ⟨(rule,index),member,rfl⟩
  cases found : environment.specifications.find? (fun entry => entry.1 == index) with
  | none =>
      have rejected := List.find?_eq_none.mp found _ mapped
      exact False.elim (rejected (beq_self_eq_true _))
  | some entry =>
      have chosen := List.mem_of_find?_eq_some found
      change entry ∈ language.rewrites.zipIdx.map (fun (row,ordinal) =>
        (ordinal,GeneralRuleBindingInference.inferredSpec row)) at chosen
      obtain ⟨⟨actual,ordinal⟩,position,rfl⟩ := List.mem_map.mp chosen
      have sameOrdinal : ordinal = index := by simpa only [beq_iff_eq] using List.find?_some found
      subst ordinal
      have actualPosition := List.mk_mem_zipIdx_iff_getElem?.mp position
      have sameRule : actual = rule := Option.some.inj (actualPosition.symm.trans declared)
      subst actual
      simp only [GeneralPremise.specification?,found,Option.map_some]

private theorem collection_element_role {rule : GrammarRule} {parameter : String}
    {kind : CollType} {element : TypeExpr} (member : rule ∈ language.terms)
    (shape : rule.bareParams = [.simple parameter (.collection kind element)]) : element = proc := by
  have present : (rule.category,kind,element) ∈ declaredCollectionRoles :=
    List.mem_filterMap.mpr ⟨rule,member,by simp only [shape]⟩
  rw [declared_collection_roles] at present
  rcases List.mem_cons.mp present with first | rest
  · exact congrArg (fun entry : String × CollType × TypeExpr => entry.2.2) first
  · rcases List.mem_cons.mp rest with second | impossible
    · exact congrArg (fun entry : String × CollType × TypeExpr => entry.2.2) second
    · cases impossible

theorem actual_collection_choices : CollectionChoiceDeterministic language := by
  intro left right leftName rightName kind leftElement rightElement leftMember rightMember leftShape rightShape _
  exact (collection_element_role leftMember leftShape).trans (collection_element_role rightMember rightShape).symm

private theorem actual_set_constructor : ∃ (rule : GrammarRule) (parameter : String),
    rule ∈ language.terms ∧ rule.bareParams = [.simple parameter (.collection .hashSet proc)] ∧
      rule.category = "Proc" := by
  have present : ("Proc",CollType.hashSet,proc) ∈ declaredCollectionRoles := by
    rw [declared_collection_roles]
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  obtain ⟨rule,member,selected⟩ := List.mem_filterMap.mp present
  split at selected <;> try cases selected
  rename_i parameter kind element shape
  simp only [Option.some.injEq,Prod.mk.injEq] at selected
  obtain ⟨category,rfl,rfl⟩ := selected
  exact ⟨rule,parameter,member,shape,category⟩

private theorem set_schema_role {free : FreeTypeContext} {bound : List TypeExpr}
    {items : List Pattern} {rest : Option String}
    (itemsTyped : Mettapedia.GSLT.LanguageDef.RestAwareTyping.ElementsHaveType language free bound items proc)
    (residual : Mettapedia.GSLT.LanguageDef.RestAwareTyping.RestHasType free .hashSet proc rest) :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType language free bound (.collection .hashSet items rest) proc := by
  obtain ⟨rule,parameter,member,shape,category⟩ := actual_set_constructor
  have typed := Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType.collectionConstructor member shape itemsTyped residual
  simpa only [category,proc] using typed

private theorem sum_schema_role {free : FreeTypeContext} {bound : List TypeExpr} {captureName rest : String}
    (value : free captureName = some proc) (residual : free rest = some (.collection .hashSet proc)) :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType language free bound
      (.collection .hashSet [.fvar captureName] (some rest)) proc :=
  set_schema_role (.cons (.fvar value) (.nil bound proc)) residual

private theorem chaos_schema_role (free : FreeTypeContext) (bound : List TypeExpr) :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType language free bound chaos proc := by
  obtain ⟨rule,declared,shape⟩ := Option.map_eq_some_iff.mp chaos_grammar_role
  have member : rule ∈ language.terms := List.mem_of_find?_eq_some declared
  simp only [Prod.mk.injEq] at shape
  obtain ⟨label,category,parameterRows,bare⟩ := shape
  have ordinary : ¬ UsesBareCollection rule := by
    rintro ⟨constructorName,kind,element,asCollection⟩
    rw [bare] at asCollection
    cases asCollection
  have arguments : Mettapedia.GSLT.LanguageDef.RestAwareTyping.ArgumentsHaveTypes
      language free bound [] rule.params := by rw [parameterRows]; exact .nil
  have typed := Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType.constructor member ordinary arguments
  simpa only [label,category,chaos,proc] using typed

theorem sum_inverse_row {binding : Option RuleBindingSpec}
    (declared : language.rewrites[1]? = some (sumRuleWith binding)) :
    DirectedInverseRow (fun schema => binderFree schema = true) environment proc 1
      (sumRuleWith binding) (GeneralRuleBindingInference.inferredSpec (sumRuleWith binding)) := by
  refine ⟨specification_of_declared declared,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · cbv
  · cbv
  · change (["S","rest","T"] : List String).Nodup
    decide +kernel
  · cbv
  · cbv
  · exact sum_schema_role (by cbv) (by cbv)
  · exact sum_schema_role (by cbv) (by cbv)
  · intro premise member
    cases (show premise = .congruence (.fvar "S") (.fvar "T") from List.mem_singleton.mp member)
    exact .step rfl rfl
  · intro premise member
    cases (show premise = .congruence (.fvar "S") (.fvar "T") from List.mem_singleton.mp member)
    trivial
  · cbv
  · cbv
  · cbv

theorem div_inverse_row {binding : Option RuleBindingSpec}
    (declared : language.rewrites[2]? = some (divRuleWith binding)) :
    DirectedInverseRow (fun schema => binderFree schema = true) environment proc 2
      (divRuleWith binding) (GeneralRuleBindingInference.inferredSpec (divRuleWith binding)) := by
  refine ⟨specification_of_declared declared,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · cbv
  · cbv
  · change ([] : List String).Nodup
    exact .nil
  · cbv
  · cbv
  · exact chaos_schema_role _ _
  · exact chaos_schema_role _ _
  · intro premise member; cases member
  · intro premise member; cases member
  · cbv
  · cbv
  · cbv

/-- Primitive row and child-source roles establish eligibility for the
existing authored witness; no child firing or target typing is assumed. -/
theorem actual_expanded_sum_eligible :
    DirectedInverseEligibility.Step (fun schema => binderFree schema = true) environment proc
      (.rule 1 [("rest",sum []),("S",chaos)]
        [.premiseStep (.rule 2 [] []) chaos [("T",chaos)]
          [("T",chaos),("rest",sum []),("S",chaos)]]) := by
  obtain ⟨sumBinding,sumDeclared⟩ := actual_sum_template
  obtain ⟨divBinding,divDeclared⟩ := actual_div_template
  apply DirectedInverseEligibility.Step.rule (rule := sumRuleWith sumBinding)
    (spec := GeneralRuleBindingInference.inferredSpec (sumRuleWith sumBinding)) sumDeclared (sum_inverse_row sumDeclared)
  apply DirectedInverseEligibility.Premises.cons
  · apply DirectedInverseEligibility.OnePremise.step (type := proc)
    · cbv
    · exact .rule divDeclared (div_inverse_row divDeclared) .nil
  · exact .nil

#print axioms actual_sum_template
#print axioms actual_div_template
#print axioms specification_of_declared
#print axioms actual_collection_choices
#print axioms sum_inverse_row
#print axioms div_inverse_row
#print axioms actual_expanded_sum_eligible


/-- Source typing is derived from the actual selected constructors and
collection role, independently of the reference step's conclusion. -/
theorem actual_expanded_source_open :
    OpenPatternWellSorted language environment.free [] proc (sum [chaos]) := by
  refine ⟨?_,?_,?_,?_⟩
  · exact (set_schema_role (.cons (chaos_schema_role _ _) (.nil [] proc)) (by trivial)).forget
  · decide +kernel
  · decide +kernel
  · change (sum [chaos]).isWellScopedAt 0 = true
    decide +kernel

private theorem actual_provider_closed :
    GeneralPremise.checkProviderClosed language environment.free environment.provider = true := by rfl

/-- The original authored RSum witness and its real later RDiv child now
reconstruct one actual typed firing with complete ordered premise history. -/
theorem actual_expanded_sum_reconstructed : ∃ trace captured completed history,
    GeneralPremise.RootFiring environment [] proc (sum [chaos]) 1 trace captured completed history (sum [chaos]) := by
  obtain ⟨index,initial,children,trace,captured,completed,history,same,fired⟩ :=
    directed_root_fromReference_recursive Engine.RelationEnv.empty (ReadsProvider.empty _)
      language_valid actual_collection_choices actual_provider_closed actual_expanded_sum_eligible
      actual_expanded_source_open actual_expanded_sum_reference
  have ordinal := congrArg (fun witness : ReferenceStep.Witness =>
    match witness with | .rule actual _ _ => actual | _ => 0) same
  change 1 = index at ordinal
  subst index
  exact ⟨trace,captured,completed,history,fired⟩

/-- The same reconstructed source occurrence is published by the existing
ordinary retained scheduler, with every matching and premise field intact. -/
theorem actual_expanded_sum_retained_receipt :
    ∃ trace captured completed history,
      GeneralPremise.RootFiring environment [] proc (sum [chaos]) 1
        trace captured completed history (sum [chaos]) ∧
      ∃ answer ∈ StructuralDescent.Scheduled.receipts
          (StructuralDescent.Scheduled.finishSource environment [] proc (sum [chaos])),
        answer.index = 1 ∧ answer.trace = trace ∧ answer.captured = captured ∧
        answer.completed = completed ∧ answer.history = history ∧ answer.target = sum [chaos] := by
  obtain ⟨trace,captured,completed,history,fired⟩ := actual_expanded_sum_reconstructed
  exact ⟨trace,captured,completed,history,fired,
    (ordinary_complete_receipts [] proc (sum [chaos]) 1 trace captured completed history (sum [chaos])).mpr fired⟩

theorem actual_sum_missing_child_refused : ¬ ReferenceStep.StepValid Engine.RelationEnv.empty language
    (sum [chaos]) (.rule 1 [("rest",sum []),("S",chaos)] []) (sum [chaos]) := by
  have absent : ∀ target,¬ ReferenceStep.StepValid Engine.RelationEnv.empty language
      (sum [chaos]) (.rule 1 [("rest",sum []),("S",chaos)] []) target := by
    intro target held
    obtain ⟨binding,selected⟩ := actual_sum_template
    cases held with
    | @rule _ _ rule _ _ _ declared _ premises =>
      have same : rule = sumRuleWith binding := Option.some.inj (declared.symm.trans selected)
      subst rule
      cases premises
  exact absent _

theorem actual_sum_wrong_conclusion_refused : ¬ ReferenceStep.StepValid Engine.RelationEnv.empty language
    (sum [chaos])
      (.rule 1 [("rest",sum []),("S",chaos)]
        [.premiseStep (.rule 2 [] []) chaos [("T",chaos)]
          [("T",chaos),("rest",sum []),("S",chaos)]]) (sum [zero]) := by
  intro held
  have wrong := (ReferenceStep.checkStep_eq_some_iff _ _ _).mpr held
  have expected := (ReferenceStep.checkStep_eq_some_iff _ _ _).mpr actual_expanded_sum_reference
  have same := Option.some.inj (expected.symm.trans wrong)
  have distinct : sum [chaos] ≠ sum [zero] := by decide +kernel
  exact distinct same

#print axioms actual_expanded_source_open
#print axioms actual_provider_closed
#print axioms actual_expanded_sum_reconstructed
#print axioms actual_expanded_sum_retained_receipt
#print axioms actual_sum_missing_child_refused
#print axioms actual_sum_wrong_conclusion_refused

end Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.ActualSum

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.ActualSum
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise RuleBinding ScopedRuleMatching CanonicalBags
open Mettapedia.GSLT.LanguageDef.WellSorted
open CollectionSelection

private theorem profile_member_fixed {kind : CollType} {items : List Pattern} {value : Pattern}
    (member : value ∈ arrange kind (items.map canon)) : canon value = value := by
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp ((arrange_mem value).mp member)
  exact canon_idempotent original

private theorem profile_one_allocation {idempotent : Bool} {items : List Pattern} {allocation : Allocation Pattern}
    (allocated : allocation ∈ tracedAllocations idempotent 1 items) :
    ∃ decision value, allocation.values = [value] ∧ allocation.decisions = [decision] ∧
      items[decision.selected]? = some value ∧
      allocation.residual = if decision.retained then items else items.eraseIdx decision.selected := by
  simp only [tracedAllocations,List.mem_flatMap,List.mem_map] at allocated
  obtain ⟨choice,selected,tail,listed,rfl⟩ := allocated
  have tailShape : tail = ⟨[],choice.residual,[]⟩ := List.mem_singleton.mp listed
  subst tail
  obtain ⟨found,_,residual⟩ := choice_valid selected
  exact ⟨⟨choice.selected,choice.retained⟩,choice.value,rfl,rfl,found,residual⟩

private theorem profile_capture_selection {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {initial final : Assignment} {items : List Pattern} {trace : List EquationalScopedReceipts.Event}
    {metaName restVariable : String} {kind : CollType}
    (unordered : kind ≠ .vec)
    (matched : EquationalScopedReceipts.Matches literalBodyComparison rule spec ambient
      .left [] 0 initial (.collection kind [.fvar metaName] (some restVariable))
      (.collection kind items none) trace final) :
    ∃ allocation selected middle,
      allocation ∈ tracedAllocations (kind == .hashSet) 1 (arrange kind items) ∧
      allocation.values = [selected] ∧
      trace = [⟨[],kind,allocation.decisions⟩] ∧
      capture? rule spec ambient 0 .left [0] initial metaName selected = some middle ∧
      GeneralScopedMatch.Extends middle final := by
  cases matched with
  | vectorRest arguments captured => exact False.elim (unordered rfl)
  | unordered notVector allocated arguments finished =>
    rename_i allocation innerTrace middle
    generalize valuesShape : allocation.values = values at arguments
    cases arguments with
    | cons head tail =>
      cases tail
      cases head with
      | capture captured =>
        refine ⟨allocation,_,middle,allocated,valuesShape,rfl,?_,?_⟩
        · simpa only [List.nil_append,captureWith?_literal] using captured
        · exact GeneralScopedMatch.captureWith_extends finished

private theorem profile_rearrange (kind : CollType) (items : List Pattern) :
    arrange kind (arrange kind items) = arrange kind items := by
  cases kind with
  | vec => rfl
  | hashBag => exact arrange_eq_of_presents (PatternLexOrder.sortLex_perm items)
  | hashSet => exact arrange_eq_of_presents (fun value => arrange_mem value)

private theorem profile_component_source {rule : RewriteRule} {ambient : Nat}
    {captured assignment : Assignment} {source child : Pattern} {kind : CollType}
    {trace : List EquationalScopedReceipts.Event}
    (unordered : kind ≠ .vec)
    (leftShape : rule.left = .collection kind [.fvar "S"] (some "rest"))
    (matched : RecursiveCollectionHandoff.canonicalMatchingInterpretation.Matches
      ⟨rule,GeneralRuleBindingInference.inferredSpec rule,ambient,.left,[],0,[],rule.left,source⟩
      trace captured)
    (extension : GeneralScopedMatch.Extends captured assignment)
    (instantiated : instantiateAt? rule (GeneralRuleBindingInference.inferredSpec rule) ambient
      (.premise 0 0 0) [] 0 assignment (.fvar "S") = some child) :
    ∃ items, canon source = .collection kind items none ∧
      ∃ decision : Decision, trace = [⟨[],kind,[decision]⟩] ∧
        items[decision.selected]? = some child ∧
        PatternTreeSize.nodes (canon child) < PatternTreeSize.nodes (canon source) := by
  change EquationalScopedReceipts.Matches literalBodyComparison rule
    (GeneralRuleBindingInference.inferredSpec rule) ambient .left [] 0 [] rule.left
    (canon source) trace captured at matched
  rw [leftShape] at matched
  have targetShape : ∃ items, canon source = .collection kind items none := by
    generalize targetEq : canon source = actualTarget at matched
    cases matched with
    | vectorRest arguments captured => exact False.elim (unordered rfl)
    | unordered notVector allocated arguments finished => exact ⟨_,rfl⟩
  obtain ⟨items,targetEq⟩ := targetShape
  rw [targetEq] at matched
  obtain ⟨allocation,selected,middle,allocated,valuesShape,traceShape,capturedAt,afterRest⟩ :=
    profile_capture_selection unordered matched
  obtain ⟨decision,value,valuesEq,decisionsEq,found,_⟩ := profile_one_allocation allocated
  have selectedEq : selected = value := (List.cons.inj (valuesShape.symm.trans valuesEq)).1
  subst value
  obtain ⟨contextual,_,_,foundCapture,readSelected⟩ :=
    GeneralRuleBindingInference.inferred_capture_interpretation capturedAt
  have foundAssignment := extension "S" contextual (afterRest "S" contextual foundCapture)
  simp only [instantiateAt?,instantiateWith?,foundAssignment] at instantiated
  change (arguments? rule (GeneralRuleBindingInference.inferredSpec rule) "S"
    (.premise 0 0 0) []).bind (fun arguments =>
      instantiateValue? contextual ambient 0 arguments) = some child at instantiated
  obtain ⟨arguments,occurrence,readChild⟩ := Option.bind_eq_some_iff.mp instantiated
  have argsEmpty := GeneralFirstOrderProjection.inferred_success_arguments_empty occurrence
  subst arguments
  have childEq : child = selected := Option.some.inj (readChild.symm.trans readSelected)
  subst child
  have fixed := canon_idempotent source
  rw [targetEq,canon_collection] at fixed
  have fixedItems : arrange kind (items.map canon) = items := by
    simpa only [Pattern.collection.injEq,true_and,and_true] using fixed
  have arrangedItems : arrange kind items = items := by
    calc
      arrange kind items = arrange kind (arrange kind (items.map canon)) :=
        congrArg (arrange kind) fixedItems.symm
      _ = arrange kind (items.map canon) := profile_rearrange kind _
      _ = items := fixedItems
  rw [arrangedItems] at found
  have foundMember : selected ∈ items := List.mem_of_getElem? found
  have fixedSelected : canon selected = selected :=
    profile_member_fixed (by rw [fixedItems];exact foundMember)
  refine ⟨items,targetEq,decision,?_,found,?_⟩
  · simpa only [decisionsEq] using traceShape
  · rw [fixedSelected,targetEq]
    exact PatternTreeSize.member_nodes_lt_collection foundMember

/-- The exact canonical allocation selects a proper member, for either retention
bit. The source capture and later premise readout refer to that same member. -/
theorem canonical_sum_selected_source {rule : RewriteRule} {ambient : Nat}
    {captured assignment : Assignment} {items : List Pattern} {child : Pattern}
    {trace : List EquationalScopedReceipts.Event}
    (declared : language.rewrites[1]? = some rule)
    (matched : RecursiveCollectionHandoff.canonicalMatchingInterpretation.Matches
      ⟨rule,GeneralRuleBindingInference.inferredSpec rule,ambient,.left,[],0,[],rule.left,sum items⟩
      trace captured)
    (extension : GeneralScopedMatch.Extends captured assignment)
    (instantiated : instantiateAt? rule (GeneralRuleBindingInference.inferredSpec rule) ambient
      (.premise 0 0 0) [] 0 assignment (.fvar "S") = some child) :
    ∃ decision : Decision,
      trace = [⟨[],.hashSet,[decision]⟩] ∧
      (arrange .hashSet (items.map canon))[decision.selected]? = some child ∧
      PatternTreeSize.nodes (canon child) < PatternTreeSize.nodes (canon (sum items)) := by
  have shapes := lowered_sum_source
  rw [declared] at shapes
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq] at shapes
  obtain ⟨canonicalItems,sourceShape,decision,traceShape,found,smaller⟩ :=
    profile_component_source (by decide) shapes.1 matched extension instantiated
  have itemsEq : canonicalItems = arrange .hashSet (items.map canon) := by
    simpa only [sum,canon_collection,Pattern.collection.injEq,true_and,and_true] using sourceShape.symm
  exact ⟨decision,traceShape,by simpa only [itemsEq] using found,smaller⟩

private theorem actual_inferred_spec {index : Nat} {rule : RewriteRule} {spec : RuleBindingSpec}
    (declared : language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec) :
    spec = GeneralRuleBindingInference.inferredSpec rule := by
  obtain ⟨entry,found,selected⟩ := Option.map_eq_some_iff.mp specified
  have listed := List.mem_of_find?_eq_some found
  obtain ⟨⟨actual,ordinal⟩,position,same⟩ := List.mem_map.mp listed
  cases same
  have ordinalEq : ordinal = index := by
    have accepted := List.find?_some found
    simpa only [beq_iff_eq] using accepted
  subst ordinal
  have actualEq : actual = rule := Option.some.inj
    ((List.mk_mem_zipIdx_iff_getElem?.mp position).symm.trans declared)
  subst actual
  exact selected.symm

/-- Intrinsic collection equality preserves this measure. Declared wrapper,
unit and singleton equations are not part of this assertion. -/
theorem canonical_source_size_same {left right : Pattern} (same : Same left right) :
    PatternTreeSize.nodes (canon left) = PatternTreeSize.nodes (canon right) :=
  congrArg PatternTreeSize.nodes same

/-- The actual interpreted sum firing retains its child event and allocation
origin while its selected child source strictly decreases canonical size. -/
theorem canonical_sum_child_bound {bound : List TypeExpr} {type : TypeExpr}
    {items : List Pattern} {trace : List EquationalScopedReceipts.Event}
    {captured completed : Assignment} {history : List (Event EquationalScopedReceipts.Event)}
    {target : Pattern}
    (fired : Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation
      environment bound type (sum items) 1 trace captured completed history target) :
    ∃ childIndex childSource childTarget childTrace targetTrace childCaptured childCompleted childHistory,
      ∃ decision : Decision, ∃ childType : TypeExpr,
      history = [.child 0 0 childIndex bound childSource childTarget childTrace targetTrace
        childCaptured childCompleted childHistory] ∧
      trace = [⟨[],.hashSet,[decision]⟩] ∧
      (arrange .hashSet (items.map canon))[decision.selected]? = some childSource ∧
      Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation environment
        bound childType childSource childIndex childTrace childCaptured childCompleted childHistory childTarget ∧
      PatternTreeSize.nodes (canon childSource) < PatternTreeSize.nodes (canon (sum items)) := by
  cases fired with
  | @fire _ _ _ _ _ rule spec _ _ _ _ declared specified _ _ matched _ premises _ _ =>
    change language.rewrites[1]? = some rule at declared
    have specEq := actual_inferred_spec declared specified
    subst spec
    have shapes := lowered_sum_source
    rw [declared] at shapes
    simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq] at shapes
    rw [shapes.2] at premises
    cases premises with
    | cons first rest =>
      cases rest
      cases first with
      | step sourceType instantiated child targetMatched targetTyped =>
        obtain ⟨decision,traceEq,selected,smaller⟩ := canonical_sum_selected_source declared matched
          (GeneralScopedMatch.Extends.refl _) instantiated
        refine ⟨_,_,_,_,_,_,_,_,decision,_,rfl,traceEq,selected,child,smaller⟩

/-- Intrinsic re-presentation changes neither the stored child event nor its
strict bound. This transport does not use authored singleton collapse. -/
theorem canonical_sum_child_event_smaller {bound childBound : List TypeExpr} {type : TypeExpr}
    {source childSource childTarget target : Pattern} {items : List Pattern}
    {trace childTrace targetTrace : List EquationalScopedReceipts.Event}
    {captured completed childCaptured childCompleted : Assignment}
    {history childHistory : List (Event EquationalScopedReceipts.Event)}
    {premiseIndex quantifierDepth childIndex : Nat}
    (same : Same source (sum items))
    (fired : Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation
      environment bound type source 1 trace captured completed history target)
    (recorded : Event.child premiseIndex quantifierDepth childIndex childBound
      childSource childTarget childTrace targetTrace childCaptured childCompleted childHistory ∈ history) :
    PatternTreeSize.nodes (canon childSource) < PatternTreeSize.nodes (canon source) := by
  have presented := RecursiveCollectionHandoff.canonical_firing_same_source same fired
  obtain ⟨_,_,_,_,_,_,_,_,_,_,historyShape,_,_,_,smaller⟩ := canonical_sum_child_bound presented
  rw [historyShape] at recorded
  cases List.mem_singleton.mp recorded
  simpa only [canonical_source_size_same same] using smaller

/-- A sum source without members cannot acquire an RSum origin by intrinsic
normalization, even though a nonempty set may retain its selected member. -/
theorem canonical_sum_empty_origin_refused {bound : List TypeExpr} {type : TypeExpr}
    {trace : List EquationalScopedReceipts.Event} {captured completed : Assignment}
    {history : List (Event EquationalScopedReceipts.Event)} {target : Pattern}
    (fired : Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation
      environment bound type (sum []) 1 trace captured completed history target) : False := by
  obtain ⟨_,_,_,_,_,_,_,_,decision,_,_,_,selected,_,_⟩ := canonical_sum_child_bound fired
  change ([] : List Pattern)[decision.selected]? = some _ at selected
  simp only [List.getElem?_nil] at selected
  cases selected

#print axioms canonical_sum_child_event_smaller
#print axioms canonical_sum_empty_origin_refused
#print axioms profile_rearrange
#print axioms actual_inferred_spec
#print axioms canonical_source_size_same
#print axioms canonical_sum_child_bound
#print axioms canonical_sum_selected_source
#print axioms profile_member_fixed
#print axioms profile_one_allocation
#print axioms profile_capture_selection
end Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.ActualSum

namespace Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.ActualSum
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise RuleBinding ScopedRuleMatching CanonicalBags
open Mettapedia.GSLT.LanguageDef.WellSorted
open CollectionSelection
private theorem profile_lift_history {bound : List TypeExpr} {type : TypeExpr}
    {source target : Pattern} {index : Nat} {rule : RewriteRule} {kind : CollType}
    {trace : List EquationalScopedReceipts.Event} {captured completed : Assignment}
    {history : List (Event EquationalScopedReceipts.Event)}
    (unordered : kind ≠ .vec)
    (declared : language.rewrites[index]? = some rule)
    (leftShape : rule.left = .collection kind [.fvar "S"] (some "rest"))
    (premisesShape : rule.premises = [.congruence (.fvar "S") (.fvar "T")])
    (fired : Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation
      environment bound type source index trace captured completed history target) :
    ∃ items childIndex childSource childTarget childTrace targetTrace childCaptured childCompleted childHistory,
      ∃ decision : Decision, ∃ childType : TypeExpr,
        canon source = .collection kind items none ∧
        history = [.child 0 0 childIndex bound childSource childTarget childTrace targetTrace
          childCaptured childCompleted childHistory] ∧
        trace = [⟨[],kind,[decision]⟩] ∧ items[decision.selected]? = some childSource ∧
        Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation environment
          bound childType childSource childIndex childTrace childCaptured childCompleted childHistory childTarget ∧
        PatternTreeSize.nodes (canon childSource) < PatternTreeSize.nodes (canon source) := by
  cases fired with
  | @fire _ _ _ _ _ actual spec _ _ _ _ actualDeclared specified _ _ matched _ premises _ _ =>
    have ruleEq : actual = rule := Option.some.inj (actualDeclared.symm.trans declared)
    subst actual
    have specEq := actual_inferred_spec declared specified
    subst spec
    rw [premisesShape] at premises
    cases premises with
    | cons head tail =>
      cases tail
      cases head with
      | step sourceType instantiated child targetMatched targetTyped =>
        obtain ⟨items,sourceShape,decision,traceShape,selected,smaller⟩ :=
          profile_component_source unordered leftShape matched (GeneralScopedMatch.Extends.refl _) instantiated
        exact ⟨items,_,_,_,_,_,_,_,_,decision,_,sourceShape,rfl,traceShape,selected,child,smaller⟩

/-- Every actual canonical child event belongs to RPar or RSum. The other
actual declarations are child-free; no declaration-order premise is used. -/
theorem canonical_child_history_profile {bound : List TypeExpr} {type : TypeExpr}
    {source target : Pattern} {index : Nat} {trace : List EquationalScopedReceipts.Event}
    {captured completed : Assignment} {history : List (Event EquationalScopedReceipts.Event)}
    (fired : Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation
      environment bound type source index trace captured completed history target) :
    history = [] ∨ ∃ childIndex childSource childTarget childTrace targetTrace childCaptured childCompleted childHistory,
      ∃ childType : TypeExpr,
        history = [.child 0 0 childIndex bound childSource childTarget childTrace targetTrace
          childCaptured childCompleted childHistory] ∧
        Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation environment
          bound childType childSource childIndex childTrace childCaptured childCompleted childHistory childTarget ∧
        PatternTreeSize.nodes (canon childSource) < PatternTreeSize.nodes (canon source) := by
  cases index with
  | zero =>
    obtain ⟨rule,declared,shape⟩ := Option.map_eq_some_iff.mp lowered_parallel_source
    simp only [Prod.mk.injEq] at shape
    obtain ⟨_,childIndex,childSource,childTarget,childTrace,targetTrace,childCaptured,childCompleted,childHistory,
        _,childType,_,historyShape,_,_,child,smaller⟩ :=
      profile_lift_history (by decide) declared shape.1 shape.2 fired
    exact .inr ⟨childIndex,childSource,childTarget,childTrace,targetTrace,childCaptured,childCompleted,
      childHistory,childType,historyShape,child,smaller⟩
  | succ index =>
    cases index with
    | zero =>
      obtain ⟨rule,declared,shape⟩ := Option.map_eq_some_iff.mp lowered_sum_source
      simp only [Prod.mk.injEq] at shape
      obtain ⟨_,childIndex,childSource,childTarget,childTrace,targetTrace,childCaptured,childCompleted,childHistory,
          _,childType,_,historyShape,_,_,child,smaller⟩ :=
        profile_lift_history (by decide) declared shape.1 shape.2 fired
      exact .inr ⟨childIndex,childSource,childTarget,childTrace,targetTrace,childCaptured,childCompleted,
        childHistory,childType,historyShape,child,smaller⟩
    | succ index =>
      cases fired with
      | fire declared _ _ _ _ _ premises _ _ =>
        change language.rewrites[index + 1 + 1]? = some _ at declared
        have listed := congrArg (fun rows => rows[index + 1 + 1]?) profile_rule_premises
        simp only [List.getElem?_map,declared,Option.map_some] at listed
        cases index with
        | zero =>
          simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at listed
          rw [listed] at premises
          cases premises
          exact .inl rfl
        | succ index =>
          cases index with
          | zero =>
            simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at listed
            rw [listed] at premises
            cases premises
            exact .inl rfl
          | succ index =>
            simp only [List.getElem?_cons_succ,List.getElem?_nil] at listed
            cases listed


private theorem profile_pending_smaller {rule : RewriteRule} {ambient premiseIndex : Nat}
    {parent child sourceSchema targetSchema : Pattern} {kind : CollType}
    {captured assignment : Assignment} {trace : List EquationalScopedReceipts.Event}
    (unordered : kind ≠ .vec)
    (leftShape : rule.left = .collection kind [.fvar "S"] (some "rest"))
    (premisesShape : rule.premises = [.congruence (.fvar "S") (.fvar "T")])
    (occurs : rule.premises[premiseIndex]? = some (.congruence sourceSchema targetSchema))
    (matched : RecursiveCollectionHandoff.canonicalMatchingInterpretation.Matches
      ⟨rule,GeneralRuleBindingInference.inferredSpec rule,ambient,.left,[],0,[],rule.left,parent⟩
      trace captured)
    (extension : GeneralScopedMatch.Extends captured assignment)
    (instantiated : instantiateAt? rule (GeneralRuleBindingInference.inferredSpec rule) ambient
      (.premise premiseIndex 0 0) [] 0 assignment sourceSchema = some child) :
    PatternTreeSize.nodes (canon child) < PatternTreeSize.nodes (canon parent) := by
  rw [premisesShape] at occurs
  cases premiseIndex with
  | zero =>
    simp only [List.getElem?_cons_zero,Option.some.injEq,Premise.congruence.injEq] at occurs
    obtain ⟨rfl,rfl⟩ := occurs
    obtain ⟨_,_,_,_,_,smaller⟩ := profile_component_source unordered leftShape matched extension instantiated
    exact smaller
  | succ index =>
    simp only [List.getElem?_cons_succ,List.getElem?_nil] at occurs
    cases occurs

/-- Every actual prepared recursive source decreases before child search
succeeds or fails. Incoming captures and the current occurrence stay fixed. -/
theorem canonical_pending_child_smaller {rule : RewriteRule} {index premiseIndex ambient : Nat}
    {parent child sourceSchema targetSchema : Pattern} {captured assignment : Assignment}
    {trace : List EquationalScopedReceipts.Event}
    (declared : language.rewrites[index]? = some rule)
    (occurs : rule.premises[premiseIndex]? = some (.congruence sourceSchema targetSchema))
    (matched : RecursiveCollectionHandoff.canonicalMatchingInterpretation.Matches
      ⟨rule,GeneralRuleBindingInference.inferredSpec rule,ambient,.left,[],0,[],rule.left,parent⟩
      trace captured)
    (extension : GeneralScopedMatch.Extends captured assignment)
    (instantiated : instantiateAt? rule (GeneralRuleBindingInference.inferredSpec rule) ambient
      (.premise premiseIndex 0 0) [] 0 assignment sourceSchema = some child) :
    PatternTreeSize.nodes (canon child) < PatternTreeSize.nodes (canon parent) := by
  cases index with
  | zero =>
    have shape := lowered_parallel_source
    rw [declared] at shape
    simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq] at shape
    exact profile_pending_smaller (by decide) shape.1 shape.2 occurs matched extension instantiated
  | succ index =>
    cases index with
    | zero =>
      have shape := lowered_sum_source
      rw [declared] at shape
      simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq] at shape
      exact profile_pending_smaller (by decide) shape.1 shape.2 occurs matched extension instantiated
    | succ index =>
      have listed := congrArg (fun rows => rows[index + 1 + 1]?) profile_rule_premises
      simp only [List.getElem?_map,declared,Option.map_some] at listed
      cases index with
      | zero =>
        simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at listed
        simp only [listed,List.getElem?_nil] at occurs
        cases occurs
      | succ index =>
        cases index with
        | zero =>
          simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at listed
          simp only [listed,List.getElem?_nil] at occurs
          cases occurs
        | succ index =>
          simp only [List.getElem?_cons_succ,List.getElem?_nil] at listed
          cases listed

#print axioms profile_pending_smaller
#print axioms canonical_pending_child_smaller

private theorem canonical_history_decreases {bound : List TypeExpr} {type : TypeExpr}
    {source target : Pattern} {index : Nat} {trace : List EquationalScopedReceipts.Event}
    {captured completed : Assignment} {history : List (Event EquationalScopedReceipts.Event)}
    (fired : Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation
      environment bound type source index trace captured completed history target) :
    ∀ child ∈ StructuralDescent.eventsChildSources history,
      PatternTreeSize.nodes (canon child) < PatternTreeSize.nodes (canon source) := by
  intro child member
  rcases canonical_child_history_profile fired with empty | nonempty
  · rw [empty,StructuralDescent.eventsChildSources.eq_1] at member
    cases member
  · obtain ⟨_,actualSource,_,_,_,_,_,_,_,historyShape,_,smaller⟩ := nonempty
    rw [historyShape,StructuralDescent.eventsChildSources.eq_2,StructuralDescent.eventChildSources.eq_3,
      StructuralDescent.eventsChildSources.eq_1,List.append_nil] at member
    cases List.mem_singleton.mp member
    exact smaller

/-- All actual canonical recursive calls decrease the intrinsic source
measure. This proof uses the real RPar/RSum captures and all four declarations. -/
theorem canonical_source_certificate : StructuralDescent.SourceMeasureCertificate
    RecursiveCollectionHandoff.canonicalMatchingExecution environment
    (fun source => PatternTreeSize.nodes (canon source)) :=
  ⟨(fun source => PatternTreeSize.nodes_positive (canon source)),
    (fun fired => canonical_history_decreases fired)⟩

/-- The earned depth covers every canonical receipt of the actual source
language, including recursive calls to the same or a later declaration. -/
theorem canonical_source_depth_bound (source : Pattern) (bound : List TypeExpr) (type : TypeExpr)
    (answer : StructuralDescent.Execution.RootAnswer environment bound type source
      RecursiveCollectionHandoff.canonicalMatchingExecution) :
    answer.requiredDepth ≤ PatternTreeSize.nodes (canon source) :=
  StructuralDescent.Measured.firing_depth_bound canonical_source_certificate source bound type answer

/-- The selected canonical matcher and existing shared scheduler enumerate
exact complete receipts at the proved intrinsic source bound. -/
theorem canonical_complete_receipts (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (index : Nat) (trace : List EquationalScopedReceipts.Event) (captured completed : Assignment)
    (history : List (Event EquationalScopedReceipts.Event)) (target : Pattern) :
    (∃ answer ∈ StructuralDescent.Scheduled.receiptsWith
        (fun value => PatternTreeSize.nodes (canon value))
        (StructuralDescent.Scheduled.finishSourceWith RecursiveCollectionHandoff.canonicalCursorCost
          (fun value => PatternTreeSize.nodes (canon value)) environment bound type source),
      answer.index = index ∧ answer.trace = trace ∧ answer.captured = captured ∧
      answer.completed = completed ∧ answer.history = history ∧ answer.target = target) ↔
    Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation environment
      bound type source index trace captured completed history target :=
  StructuralDescent.Scheduled.finishSourceWith_occurrences
    RecursiveCollectionHandoff.canonicalCursorCost RecursiveCollectionHandoff.canonicalCursorLaws
    RecursiveCollectionHandoff.canonical_answer_representation canonical_source_certificate
    bound type source index trace captured completed history target

#print axioms canonical_history_decreases
#print axioms canonical_source_certificate
#print axioms canonical_source_depth_bound
#print axioms canonical_complete_receipts

#print axioms lowered_parallel_source
#print axioms profile_rule_premises
#print axioms profile_component_source
#print axioms profile_lift_history
#print axioms canonical_child_history_profile
end Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.ActualSum
