import Mettapedia.Languages.MeTTa.SpaceTheory.HEContextEntry
import Mettapedia.Languages.MeTTa.SpaceTheory.HENativeOnTransform

/-!
# Explicit HE context instructions on Transform

One port reads the possible identities of a handle and prepares the
child's request without evaluating it. A separate port reads the active
identity's handle. The rules push the saved parent or produce the
returned batch themselves. Neither port receives the enclosing
continuation, publication history, or a source execution judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEContextOnTransform

open Mettapedia.Languages.MeTTa.OSLFCore (GroundedValue)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result WorldServices)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Continuation Task)
open Mettapedia.Languages.MeTTa.HE.ContextualData (taskData taskData_injective)
open HEFocused (Parent)
open HEContextEntry (Request Instruction)
open HENativeOnTransform
  (Presentation atom atom_injective commonFields workFields parentField parentsField stackField historyField
    answerField returnAtom ordinaryTag ordinaryAtom)
open Mettapedia.GSLT.Compilation.RootRewritesOnTheStep (appTerm symTerm inst_appTerm inst_symTerm)
open Mettapedia.GSLT.Compilation.Uniform
open StateRulesOnTheStep (packet pattern packet_eq_iff instantiate_fields instantiate_packet instance_var)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic (Tm)
open RuleSyntax.ComputedConditions (Relations RelationStep Condition RuleWithCondition)

variable {Context World : Type}

def requestTag (request : Request) : Nat :=
  match request.instruction with
  | .contextSpace => 5
  | .evalc .. | .metta .. => 4

theorem enters_tag (policy : Policy) {request : Request} {child : Task} {handle}
    (opened : request.childTask policy = some (handle, child)) : requestTag request = 4 := by
  cases is : request.instruction <;> simp_all [Request.childTask, requestTag]

theorem current_tag (policy : Policy) {request : Request}
    (read : request.childTask policy = none) : requestTag request = 5 := by
  cases is : request.instruction <;> simp_all [Request.childTask, requestTag]

theorem tag_not_return (request : Request) : requestTag request ≠ 2 := by
  cases is : request.instruction <;> simp [requestTag, is]

theorem tag_not_native (request : Request) : requestTag request ≠ 1 := by
  cases is : request.instruction <;> simp [requestTag, is]

theorem tag_not_ordinary (request : Request) : requestTag request ≠ 3 := by
  cases is : request.instruction <;> simp [requestTag, is]

theorem tag_not_typed (request : Request) : requestTag request ≠ 6 := by
  cases is : request.instruction <;> simp [requestTag, is]

theorem tag_not_invocation (request : Request) : requestTag request ≠ 7 := by
  cases is : request.instruction <;> simp [requestTag, is]

theorem tag_not_body (request : Request) : requestTag request ≠ 8 := by
  cases is : request.instruction <;> simp [requestTag, is]

theorem tag_not_application (request : Request) : requestTag request ≠ 9 := by
  cases is : request.instruction <;> simp [requestTag, is]

theorem tag_not_snapshot (request : Request) : requestTag request ≠ 10 := by
  cases is : request.instruction <;> simp [requestTag, is]

theorem child_is_ordinary (policy : Policy) {request : Request} {child : Task} {handle}
    (opened : request.childTask policy = some (handle, child)) :
    HEFocused.NativeRequest.recognize child = none ∧ Request.recognize child = none := by
  cases is : request.instruction <;> simp [Request.childTask, is] at opened
  all_goals
    obtain ⟨_, rfl⟩ := opened
    exact ⟨rfl, rfl⟩

def requestAtom (code : Presentation Context World) (request : Request) (world : World) (scope : Context)
    (stack : List Continuation) (parents : List (Parent Context)) (emitted : List Result) : Expr :=
  packet (requestTag request) (workFields code request.task world scope stack parents emitted)

private theorem task_injective : Function.Injective Request.task := by
  intro first second equal
  have recognized := congrArg Request.recognize equal
  simpa only [Request.recognize_task, Option.some.injEq] using recognized

/-- One concrete identity choice per returned handle match. The returned
task is only the primitive operand/readout preparation of the instruction. -/
def enterRead (code : Presentation Context World) (services : WorldServices Context World) (policy : Policy)
    (asked : List Expr) (result : Expr) : Prop :=
  ∃ (request : Request) (handle : GroundedValue) (task : Task) (child : Context),
    asked = [atom (taskData request.task)] ∧ request.childTask policy = some (handle, task) ∧
      services.contextPayload child = handle ∧ result = .app (atom (code.context child))
        (.app (.sym (ordinaryTag task)) (atom (taskData task)))

def currentRead (code : Presentation Context World) (services : WorldServices Context World) (policy : Policy)
    (asked : List Expr) (result : Expr) : Prop :=
  ∃ (scope : Context) (request : Request),
    asked = [atom (code.context scope), atom (taskData request.task)] ∧ request.childTask policy = none ∧
      result = answerField [(.grounded (services.contextPayload scope), request.frame)]

def operations (code : Presentation Context World) (services : WorldServices Context World) (policy : Policy) :
    Relations
  | 1, asked, reply => enterRead code services policy asked reply
  | 2, asked, reply => currentRead code services policy asked reply
  | _, _, _ => False

private def enterInput : Tm := pattern 4 ([0, 1, 2, 3, 4, 5].map .var)

private def enterOutput : Tm :=
  appTerm (.var 7) (([.var 0, .var 6, symTerm 0,
    appTerm (appTerm (.var 1) (.var 2)) (.var 3), .var 4, .var 8] : List Tm).foldr appTerm (symTerm 0))

private def enterAsk : Condition Nat Tm :=
  { name := 1, arguments := [.var 5], value := appTerm (.var 6) (appTerm (.var 7) (.var 8)) }

def enterRule : RuleWithCondition Nat Tm := StateRulesOnTheStep.rule enterInput enterOutput [enterAsk]

private def currentInput : Tm := pattern 5 ([0, 1, 2, 3, 4, 5].map .var)

private def currentOutput : Tm := pattern 2 ([0, 1, 2, 3, 4, 6].map .var)

private def currentAsk : Condition Nat Tm :=
  { name := 2, arguments := [.var 1, .var 5], value := .var 6 }

def currentRule : RuleWithCondition Nat Tm := StateRulesOnTheStep.rule currentInput currentOutput [currentAsk]

theorem enters_only_tag {rel : Relations} {tag : Nat} {items : List Expr} {after : Multiset Expr}
    (step : RelationStep rel enterRule {packet tag items} after) : 4 = tag :=
  StateRulesOnTheStep.input_tag step

theorem current_only_tag {rel : Relations} {tag : Nat} {items : List Expr} {after : Multiset Expr}
    (step : RelationStep rel currentRule {packet tag items} after) : 5 = tag :=
  StateRulesOnTheStep.input_tag step

theorem asks_enter (c : Condition Nat Tm) (member : c ∈ enterRule.conditions) : c.name = 1 := by
  obtain rfl : c = enterAsk := List.mem_singleton.mp member
  rfl

theorem asks_current (c : Condition Nat Tm) (member : c ∈ currentRule.conditions) : c.name = 2 := by
  obtain rfl : c = currentAsk := List.mem_singleton.mp member
  rfl

theorem enter_restricted : enterRule.RangeRestrictedWith := by
  apply StateRulesOnTheStep.restricted
  intro x
  change x ∈ ([7, 0, 6, 1, 2, 3, 4, 8] : List Nat) →
    x ∈ ([0, 1, 2, 3, 4, 5] : List Nat) ∨ ∃ ask ∈ [enterAsk], x ∈ RuleSyntax.Machines.unknowns ask.value
  simp only [List.mem_singleton, exists_eq_left, show RuleSyntax.Machines.unknowns enterAsk.value = [6, 7, 8] from rfl]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem current_restricted : currentRule.RangeRestrictedWith := by
  apply StateRulesOnTheStep.restricted
  intro x
  change x ∈ ([0, 1, 2, 3, 4, 6] : List Nat) →
    x ∈ ([0, 1, 2, 3, 4, 5] : List Nat) ∨ ∃ ask ∈ [currentAsk], x ∈ RuleSyntax.Machines.unknowns ask.value
  simp only [List.mem_singleton, exists_eq_left, show RuleSyntax.Machines.unknowns currentAsk.value = [6] from rfl]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem enter_exact (code : Presentation Context World) (services : WorldServices Context World) (policy : Policy)
    (request : Request) (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) (after : Multiset Expr) :
    RelationStep (operations code services policy) enterRule
      {requestAtom code request world scope stack parents emitted} after ↔
    ∃ handle task child, request.childTask policy = some (handle, task) ∧ services.contextPayload child = handle ∧
      after = {ordinaryAtom code task world child [] (⟨scope, stack⟩ :: parents) emitted} := by
  rw [enterRule, StateRulesOnTheStep.instance_iff]
  constructor
  · rintro ⟨v, matched, conditions, out⟩
    simp only [enterInput, instantiate_packet, instance_var,
      requestAtom, workFields, commonFields, List.cons_append, List.nil_append, List.map_cons,
      List.map_nil, packet_eq_iff, List.cons.injEq, and_true] at matched
    obtain ⟨_, w, s, k, p, h, i⟩ := matched
    have selected := conditions enterAsk List.mem_cons_self
    simp only [enterAsk, instance_var, inst_appTerm, List.map_cons, List.map_nil, i] at selected
    obtain ⟨actual, handle, task, child, input, prepared, allowed, result⟩ := selected
    have eq : request = actual := task_injective (taskData_injective (atom_injective (List.cons.inj input).1))
    subst actual
    obtain ⟨childID, placement⟩ := Expr.app.inj result
    obtain ⟨tag, body⟩ := Expr.app.inj placement
    refine ⟨handle, task, child, prepared, allowed, ?_⟩
    simpa only [enterOutput, ordinaryAtom, packet, workFields, commonFields, List.cons_append, List.nil_append,
      instantiate_fields, instance_var, inst_symTerm, inst_appTerm, List.map_cons, List.map_nil,
      HENativeOnTransform.stackField_nil, w, s, k, p, h, childID, tag, body,
      parentsField, StateRulesOnTheStep.spine_cons, parentField] using out
  · rintro ⟨handle, task, child, prepared, allowed, rfl⟩
    let slots := workFields code request.task world scope stack parents emitted ++
      [atom (code.context child), .sym (ordinaryTag task), atom (taskData task)]
    let v := fun n : Nat => slots[n]?.getD (.sym 0)
    refine ⟨v, ?_, ?_, ?_⟩
    · simp [enterInput, instantiate_packet, instance_var, requestAtom, enters_tag policy prepared, workFields,
        commonFields, v, slots]
    · intro condition member
      obtain rfl : condition = enterAsk := List.mem_singleton.mp member
      refine ⟨request, handle, task, child, ?_, prepared, allowed, ?_⟩
      all_goals simp [enterAsk, instance_var, v, slots, workFields, commonFields]
    · simp [enterOutput, instance_var, ordinaryAtom, packet, workFields, commonFields, v, slots]
      rfl

theorem current_exact (code : Presentation Context World) (services : WorldServices Context World) (policy : Policy)
    (request : Request) (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) (after : Multiset Expr) :
    RelationStep (operations code services policy) currentRule
      {requestAtom code request world scope stack parents emitted} after ↔
    request.childTask policy = none ∧
      after = {returnAtom code world scope [(.grounded (services.contextPayload scope), request.frame)]
        stack parents emitted} := by
  rw [currentRule, StateRulesOnTheStep.instance_iff]
  constructor
  · rintro ⟨v, matched, conditions, out⟩
    simp only [currentInput, instantiate_packet, instance_var,
      requestAtom, workFields, commonFields, List.cons_append, List.nil_append, List.map_cons,
      List.map_nil, packet_eq_iff, List.cons.injEq, and_true] at matched
    obtain ⟨_, w, s, k, p, h, i⟩ := matched
    have selected := conditions currentAsk List.mem_cons_self
    simp only [currentAsk, instance_var, List.map_cons, List.map_nil, s, i] at selected
    obtain ⟨localScope, actual, input, prepared, result⟩ := selected
    obtain ⟨scopeEq, taskEq⟩ := List.cons.inj input
    obtain rfl : scope = localScope := code.context_injective (atom_injective scopeEq)
    obtain rfl : request = actual := task_injective (taskData_injective (atom_injective (List.cons.inj taskEq).1))
    refine ⟨prepared, ?_⟩
    simpa only [currentOutput, returnAtom, commonFields, List.cons_append, List.nil_append, instantiate_packet,
      List.map_map, Function.comp_def, instance_var, List.map_cons, List.map_nil, w, s, k, p, h, result] using out
  · rintro ⟨read, rfl⟩
    let slots := workFields code request.task world scope stack parents emitted ++
      [answerField [(.grounded (services.contextPayload scope), request.frame)]]
    let v := fun n : Nat => slots[n]?.getD (.sym 0)
    refine ⟨v, ?_, ?_, ?_⟩
    · simp [currentInput, instantiate_packet, instance_var, requestAtom, current_tag policy read,
        workFields, commonFields, v, slots]
    · intro condition member
      obtain rfl : condition = currentAsk := List.mem_singleton.mp member
      refine ⟨scope, request, ?_, read, ?_⟩
      all_goals simp [currentAsk, instance_var, v, slots, workFields, commonFields]
    · simp [currentOutput, instantiate_packet, instance_var, returnAtom, workFields, commonFields, v, slots]

end Mettapedia.Languages.MeTTa.SpaceTheory.HEContextOnTransform
