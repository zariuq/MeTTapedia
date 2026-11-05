import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLeafAdmission

/-!
# The counted EU query's actual collapse-child frame

Collapse retains the original equations and derives a new result name from
the complete source/scope support. Retargeting result metadata does not alter
the authored query or payload syntax. The outer caller remains saved by the
collector; its destination and pending goals need not themselves be fresh.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCountedFrame

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open FlatQueryRowCodec (Codec)
open ClosedOnceQueryFrame (FreshFor)
open GuardedCountSource (Input)
open CTLUntilScopedRound (Query Frame Fixed Decoded)
open CTLUntilAdmissionFrame (AdmissionFrame)
open CTLUntilLeafAdmission (GuardProfile)
open CTLUntilSourceRows (number)
open NestedQuerySource (Leg)

variable {Context Label : Type}

def childQuery (input : Input Context) (query : Query) : Query :=
  {query with names := {query.names with result := input.childName}}

theorem child_template (input : Input Context) (query : Query) (template : input.template = query.template) :
    (childQuery input query).template = input.childTemplate := by
  simp only [GuardedCountSource.Input.childTemplate, template]
  rfl

theorem child_legs (input : Input Context) (query : Query) : (childQuery input query).legs = query.legs := rfl

theorem child_handles (input : Input Context) (query : Query) : (childQuery input query).handles = query.handles := rfl

theorem child_source (input : Input Context) (query : Query) :
    (childQuery input query).template.source = query.template.source := rfl

theorem child_body (input : Input Context) (query : Query)
    (template : input.template = query.template) (legs : input.legs = query.legs) :
    ScopedNestedQueryExecution.source (childQuery input query).legs (childQuery input query).template.source = input.body := by
  rw [child_legs, child_source]
  simp only [GuardedCountSource.Input.body, template, legs]

theorem child_bindings (input : Input Context) : input.childCaller.bindings = input.caller.bindings := rfl

theorem child_result_fresh (input : Input Context) : FreshFor input.childName input.childCaller.bindings := by
  apply ClosedOnceQueryFrame.fresh_for_bindings input.preparing
  intro member
  exact childName_fresh input.preparing input.boundary (Finset.mem_union_left _ member)

private theorem nested_retains_body (legs : List Leg) (body : Atom) (name : String)
    (used : name ∈ (encode body).freeVars) :
    name ∈ (encode (ScopedNestedQueryExecution.source legs body)).freeVars := by
  induction legs with
  | nil => exact used
  | cons leg rest ih =>
    rw [ScopedNestedQueryExecution.source, ScopedMatchPreparation.source, CapturedPatternSupport.mem_expression_names]
    exact ⟨ScopedNestedQueryExecution.source rest body, by simp, ih⟩

private theorem nested_retains_pattern (legs : List Leg) (body : Atom) (leg : Leg) (name : String)
    (present : leg ∈ legs) (used : name ∈ (encode leg.2).freeVars) :
    name ∈ (encode (ScopedNestedQueryExecution.source legs body)).freeVars := by
  revert present
  induction legs with
  | nil => intro impossible; cases impossible
  | cons first rest ih =>
    intro present
    rw [ScopedNestedQueryExecution.source, ScopedMatchPreparation.source, CapturedPatternSupport.mem_expression_names]
    rcases List.mem_cons.mp present with same | later
    · subst leg
      exact ⟨first.2, by simp, used⟩
    · exact ⟨ScopedNestedQueryExecution.source rest body, by simp, ih later⟩

private theorem local_names_in_body (query : Query) (name : String)
    (present : name ∈ [query.names.next, query.names.prior, query.names.temporary]) :
    name ∈ (encode (ScopedNestedQueryExecution.source query.legs query.template.source)).freeVars := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl
  · apply nested_retains_pattern query.legs query.template.source query.frontier query.names.next (by simp [Query.legs])
    change query.names.next ∈ (encode (CTLUntilScopedCapture.frontierCode query.names.formula query.currentRound query.names.next)).freeVars
    rw [CTLUntilScopedCapture.frontierCode, CapturedPatternSupport.mem_expression_names]
    exact ⟨.var query.names.next, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩
  · apply nested_retains_pattern query.legs query.template.source query.edge query.names.prior (by simp [Query.legs])
    change query.names.prior ∈ (encode (CTLUntilSourceRows.reversePattern query.names.next query.names.prior)).freeVars
    rw [CTLUntilSourceRows.reversePattern, CapturedPatternSupport.mem_expression_names]
    exact ⟨.var query.names.prior, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩
  · apply nested_retains_body
    rw [GuardedNestedQuerySource.Template.source, CapturedPatternSupport.mem_expression_names]
    refine ⟨ScopedInsertionSequence.source query.template.body.temporary query.template.satisfactionHandle
      query.template.body.secondHandle query.template.body.firstCode query.template.body.secondCode, by simp, ?_⟩
    rw [ScopedInsertionSequence.source, CapturedPatternSupport.mem_expression_names]
    exact ⟨.var query.names.temporary, by simp [Query.template], by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩

theorem child_name_apart (input : Input Context) (query : Query)
    (template : input.template = query.template) (legs : input.legs = query.legs) (name : String)
    (present : name ∈ [query.names.next, query.names.prior, query.names.temporary]) : input.childName ≠ name := by
  have used : name ∈ (encode input.body).freeVars := by
    simpa only [GuardedCountSource.Input.body, template, legs] using local_names_in_body query name present
  have collection : name ∈ (encode input.collection).freeVars := by
    rw [GuardedCountSource.Input.collection, CapturedPatternSupport.mem_expression_names]
    exact ⟨input.body, by simp, used⟩
  have retained := GuardedInsertionPairSource.goal_atom_support input.preparing input.collection name
    (by simp [GuardedCountSource.Input.preparing, Goal.atoms]) collection
  intro same
  rw [← same] at retained
  exact childName_fresh input.preparing input.boundary (Finset.mem_union_left _ retained)

theorem child_names_distinct (input : Input Context) (query : Query)
    (template : input.template = query.template) (legs : input.legs = query.legs)
    (distinct : [query.names.next, query.names.prior, query.names.temporary].Nodup) :
    [(childQuery input query).names.next, (childQuery input query).names.prior,
      (childQuery input query).names.result, (childQuery input query).names.temporary].Nodup := by
  have nextApart := Ne.symm (child_name_apart input query template legs query.names.next (by simp))
  have priorApart := Ne.symm (child_name_apart input query template legs query.names.prior (by simp))
  have temporaryApart := child_name_apart input query template legs query.names.temporary (by simp)
  change [query.names.next, query.names.prior, input.childName, query.names.temporary].Nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at distinct ⊢
  tauto

/-- The source-created child is admitted without assuming a fresh original
result or an empty outer continuation. Its generated result supplies both. -/
theorem child_admission (codec : Codec Label) (label operand : Label) (round : Nat)
    (input : Input Context) (query : Query)
    (template : input.template = query.template) (legs : input.legs = query.legs)
    (principal : Environment) (resolved : resolve input.caller.bindings = some principal)
    (formula : read principal (.var query.names.formula) = codec.encode label)
    (holds : read principal (.var query.operand) = codec.encode operand)
    (current : read principal (.var query.currentRound) = number round)
    (next : read principal (.var query.names.nextRound) = number (round + 1))
    (nextFresh : FreshFor query.names.next input.caller.bindings)
    (priorFresh : FreshFor query.names.prior input.caller.bindings)
    (temporaryFresh : FreshFor query.names.temporary input.caller.bindings)
    (distinct : [query.names.next, query.names.prior, query.names.temporary].Nodup) :
    AdmissionFrame codec label operand round (childQuery input query) (childQuery input query).legs input.childCaller ∧
      [(childQuery input query).names.next, (childQuery input query).names.prior,
        (childQuery input query).names.result, (childQuery input query).names.temporary].Nodup := by
  refine ⟨?_, child_names_distinct input query template legs distinct⟩
  refine ⟨Frame.frontier input.childCaller ⟨principal, resolved⟩ ?_ nextFresh priorFresh,
    child_result_fresh input, temporaryFresh, rfl, rfl⟩
  exact CTLUntilScopedRound.fixed_of_readings codec label operand round (childQuery input query)
    input.childCaller principal resolved formula holds current next

def childProfile (codec : Codec Label) (label : Label) (input : Input Context) (query : Query)
    (profile : GuardProfile codec label query input.program) : GuardProfile codec label (childQuery input query) input.program where
  occurrence := profile.occurrence
  row := profile.row
  otherHeads := profile.otherHeads
  leftEvaluated := profile.leftEvaluated
  rightEvaluated := profile.rightEvaluated

theorem child_decoded (codec : Codec Label) (input : Input Context) (query : Query)
    (valid : Decoded codec query.handles input.state) : Decoded codec (childQuery input query).handles input.childState := valid

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCountedFrame
