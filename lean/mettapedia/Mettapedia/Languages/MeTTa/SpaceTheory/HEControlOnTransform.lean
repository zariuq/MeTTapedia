import Mettapedia.Languages.MeTTa.SpaceTheory.HEContextOnTransform
import Mettapedia.Languages.MeTTa.SpaceTheory.HEAtomOnTransform
import Mettapedia.Languages.MeTTa.SpaceTheory.HEInvocationOnTransform
import Mettapedia.Languages.MeTTa.SpaceTheory.HEBodyReturnOnTransform
import Mettapedia.Languages.MeTTa.SpaceTheory.HEApplicationEntry
import Mettapedia.Languages.MeTTa.SpaceTheory.HEMinimalEntry
import Mettapedia.GSLT.Core.OperationalPathFibration

/-!
# Focused HE evaluation on one Transform program

Invocation, body evaluation, and ordinary continuation consumption use
the same focused term. Only the nearest continuation sees a returning
batch. With no local continuation, returning to a parent transfers the
complete batch; publication instead takes one occurrence at the root.
The history is reversed so a publication adds one constructor regardless
of the length of the already published history.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEControlOnTransform

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.Compilation.RootRewritesOnTheStep (appTerm symTerm inst_appTerm inst_symTerm)
open Mettapedia.GSLT.Compilation.Uniform
open StateRulesOnTheStep (packet packet_eq_iff pattern instantiate_packet instance_var)
open PureContinuationRules (Width)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
  (Policy Result WorldEnvironment WorldServices)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (WorldStepWith)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Continuation Task WorldConfiguration)
open Mettapedia.Languages.MeTTa.HE.ContextualData (taskData taskData_injective resultData)
open HEFocused (Focus Leaf Parent NativeRequest)
open HEWorkView (workView workTag_not_return)
open HENativeOnTransform
  (Presentation atom commonFields workFields nativeExtras stackField parentField parentsField historyField
    answerField requestAtom returnAtom ordinaryAtom ordinaryTag)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic (Tm SState inst readsAs_unique)
open RuleSyntax.Machines (ReadsBag)
open RuleSyntax.ComputedConditions
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)

variable {Context World : Type}

/-! ## The two structural rules -/

private def resumeInput : Tm :=
  pattern 2 [.var 0, .var 1, symTerm 0, appTerm (appTerm (.var 2) (.var 3)) (.var 4), .var 5, .var 6]

private def resumeOutput : Tm := pattern 2 ([0, 2, 3, 4, 5, 6].map .var)

def resumeRule : RuleWithCondition Nat Tm := StateRulesOnTheStep.rule resumeInput resumeOutput []

private def publishInput : Tm :=
  pattern 2 [.var 0, .var 1, symTerm 0, symTerm 0, .var 2, appTerm (.var 3) (.var 4)]

private def publishOutput : Tm :=
  pattern 2 [.var 0, .var 1, symTerm 0, symTerm 0, appTerm (.var 3) (.var 2), .var 4]

def publishRule : RuleWithCondition Nat Tm := StateRulesOnTheStep.rule publishInput publishOutput []

private theorem resume_restricted : resumeRule.RangeRestrictedWith := by
  unfold resumeRule
  apply StateRulesOnTheStep.unconditional_restricted
  change ([0, 2, 3, 4, 5, 6] : List Nat) ⊆ [0, 1, 2, 3, 4, 5, 6]
  intro x
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem publish_restricted : publishRule.RangeRestrictedWith := by
  unfold publishRule
  apply StateRulesOnTheStep.unconditional_restricted
  change ([0, 1, 3, 2, 4] : List Nat) ⊆ [0, 1, 2, 3, 4]
  intro x
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem resume_tag {rel : Relations} {tag : Nat} {items : List Expr} {after : Multiset Expr}
    (step : RelationStep rel resumeRule {packet tag items} after) : 2 = tag :=
  StateRulesOnTheStep.input_tag step

private theorem publish_tag {rel : Relations} {tag : Nat} {items : List Expr} {after : Multiset Expr}
    (step : RelationStep rel publishRule {packet tag items} after) : 2 = tag :=
  StateRulesOnTheStep.input_tag step

theorem resume_rewrite_iff (code : Presentation Context World) (rel : Relations)
    (world : World) (scope : Context) (answers : List Result) (stack : List Continuation)
    (parents : List (Parent Context)) (published : List Result) (after : Multiset Expr) :
    RelationStep rel resumeRule {returnAtom code world scope answers stack parents published} after ↔
      ∃ parent outer, stack = [] ∧ parents = parent :: outer ∧
        after = {returnAtom code world parent.scope answers parent.stack outer published} := by
  rw [resumeRule, StateRulesOnTheStep.instance_iff]
  constructor
  · rintro ⟨values, matched, _, output⟩
    simp only [resumeInput, returnAtom, commonFields, List.cons_append, List.nil_append,
      instantiate_packet, List.map_cons, List.map_nil,
      instance_var, inst_symTerm, inst_appTerm, packet_eq_iff, true_and, List.cons.injEq, and_true] at matched
    obtain ⟨w, _, empty, ancestor, seen, pending⟩ := matched
    have stackEmpty : stack = [] := HENativeOnTransform.stackField_injective empty.symm
    cases parents with
    | nil => cases ancestor
    | cons parent outer =>
      change Expr.app (Expr.app (values 2) (values 3)) (values 4) =
        Expr.app (parentField code parent) (parentsField code outer) at ancestor
      obtain ⟨head, tail⟩ := Expr.app.inj ancestor
      obtain ⟨parentScope, parentStack⟩ := Expr.app.inj head
      refine ⟨parent, outer, stackEmpty, rfl, ?_⟩
      simpa only [resumeOutput, returnAtom, commonFields, List.cons_append, List.nil_append,
        instantiate_packet, List.map_map, Function.comp_def,
        List.map_cons, List.map_nil, instance_var, w, parentScope, parentStack, tail, seen, pending] using output
  · rintro ⟨parent, outer, rfl, rfl, rfl⟩
    let items := [atom (code.world world), atom (code.context scope), atom (code.context parent.scope),
      stackField parent.stack, parentsField code outer, historyField published, answerField answers]
    let values := fun n : Nat => items[n]?.getD (.sym 0)
    refine ⟨values, ?_, by simp, ?_⟩
    · simp [resumeInput, instantiate_packet, instance_var, returnAtom, commonFields, values, items]
      rfl
    · simp [resumeOutput, instantiate_packet, instance_var, returnAtom, commonFields, values, items]

theorem publish_rewrite_iff (code : Presentation Context World) (rel : Relations)
    (world : World) (scope : Context) (answers : List Result) (stack : List Continuation)
    (parents : List (Parent Context)) (published : List Result) (after : Multiset Expr) :
    RelationStep rel publishRule {returnAtom code world scope answers stack parents published} after ↔
      ∃ first rest, stack = [] ∧ parents = [] ∧ answers = first :: rest ∧
        after = {returnAtom code world scope rest [] [] (published ++ [first])} := by
  rw [publishRule, StateRulesOnTheStep.instance_iff]
  constructor
  · rintro ⟨values, matched, _, output⟩
    simp only [publishInput, returnAtom, commonFields, List.cons_append, List.nil_append,
      instantiate_packet, List.map_cons, List.map_nil,
      instance_var, inst_symTerm, inst_appTerm, packet_eq_iff, true_and, List.cons.injEq, and_true] at matched
    obtain ⟨w, c, empty, root, seen, pending⟩ := matched
    have stackEmpty : stack = [] := HENativeOnTransform.stackField_injective empty.symm
    have noParents : parents = [] := (HENativeOnTransform.parentsField_injective code) root.symm
    cases answers with
    | nil => cases pending
    | cons first rest =>
      change Expr.app (values 3) (values 4) =
        Expr.app (atom (resultData first)) (answerField rest) at pending
      obtain ⟨head, tail⟩ := Expr.app.inj pending
      refine ⟨first, rest, stackEmpty, noParents, rfl, ?_⟩
      simpa only [publishOutput, returnAtom, commonFields, List.cons_append, List.nil_append,
        instantiate_packet, List.map_cons, List.map_nil,
        instance_var, inst_symTerm, inst_appTerm, w, c, seen, head, tail,
        HENativeOnTransform.historyField_emit, HENativeOnTransform.stackField_nil,
        HENativeOnTransform.parentsField_nil]
        using output
  · rintro ⟨first, rest, rfl, rfl, rfl, rfl⟩
    let items := [atom (code.world world), atom (code.context scope), historyField published,
      atom (resultData first), answerField rest]
    let values := fun n : Nat => items[n]?.getD (.sym 0)
    refine ⟨values, ?_, by simp, ?_⟩
    · simp [publishInput, instantiate_packet, instance_var, returnAtom, commonFields, values, items]
      rfl
    · simp [publishOutput, instantiate_packet, instance_var, returnAtom, commonFields, values, items]

/-! ## A single code for an entire mixed run -/

def encodeFocus (code : Presentation Context World) (state : Focus Context World) : Expr :=
  match state.leaf with
  | .work task =>
    packet (workView task).1 (workFields code task state.world state.scope state.stack state.parents
      state.emitted (workView task).2)
  | .returning answers => returnAtom code state.world state.scope answers state.stack state.parents state.emitted

@[simp] theorem encode_native (code : Presentation Context World) (request : NativeRequest) (world : World)
    (scope : Context) (stack : List Continuation) (parents : List (Parent Context)) (emitted : List Result) :
    encodeFocus code ⟨world, scope, .work request.task, stack, parents, emitted⟩ =
      requestAtom code request world scope stack parents emitted := by
  simp only [encodeFocus, workView, NativeRequest.recognize_task]
  rfl

@[simp] theorem encode_scope (code : Presentation Context World) (request : HEContextEntry.Request)
    (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) :
    encodeFocus code ⟨world, scope, .work request.task, stack, parents, emitted⟩ =
      HEContextOnTransform.requestAtom code request world scope stack parents emitted := by
  simp only [encodeFocus, workView, HEContextEntry.not_native, HEContextEntry.Request.recognize_task]
  rfl

theorem encode_ordinary (code : Presentation Context World) (task : Task)
    (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result)
    (notNative : NativeRequest.recognize task = none) (notScope : HEContextEntry.Request.recognize task = none) :
    encodeFocus code ⟨world, scope, .work task, stack, parents, emitted⟩ =
      ordinaryAtom code task world scope stack parents emitted := by
  simp only [encodeFocus, workView, notNative, notScope]
  rfl

@[simp] theorem encode_atom (code : Presentation Context World) (request : HEAtomEntry.Request)
    (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) :
    encodeFocus code ⟨world, scope, .work request.task, stack, parents, emitted⟩ =
      HEAtomOnTransform.requestAtom code request world scope stack parents emitted := by
  cases request
  rfl

@[simp] theorem encode_invocation (code : Presentation Context World) (request : HEInvocationEntry.Request)
    (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) :
    encodeFocus code ⟨world, scope, .work request.task, stack, parents, emitted⟩ =
      HEInvocationOnTransform.requestAtom code request world scope stack parents emitted := by
  cases request with
  | invoke q mode => cases mode <;> rfl
  | retained q expected work => cases expected <;> rfl

theorem encode_body (code : Presentation Context World) (task : Task) (world : World)
    (scope : Context) (stack : List Continuation) (parents : List (Parent Context))
    (emitted : List Result) (supported : HEBodyEntry.covered task = true) :
    encodeFocus code ⟨world, scope, .work task, stack, parents, emitted⟩ =
      HEBodyReturnOnTransform.requestAtom code task world scope stack parents emitted := by
  cases task <;> first | rfl | cases supported

theorem encode_application (code : Presentation Context World) (task : Task) (world : World)
    (scope : Context) (stack : List Continuation) (parents : List (Parent Context))
    (emitted : List Result) (supported : HEApplicationEntry.covered task = true) :
    encodeFocus code ⟨world, scope, .work task, stack, parents, emitted⟩ =
      packet 9 (workFields code task world scope stack parents emitted) := by
  cases task <;> first | rfl | cases supported

@[simp] theorem encode_return (code : Presentation Context World) (world : World)
    (scope : Context) (answers : List Result) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) :
    encodeFocus code ⟨world, scope, .returning answers, stack, parents, emitted⟩ =
      returnAtom code world scope answers stack parents emitted := rfl

/-- The unified code retains the complete configuration, not just the
currently observable answer list. The named-world code separates identities
even when their present definition views coincide. -/
theorem encodeFocus_injective (code : Presentation Context World) : Function.Injective (encodeFocus code) := by
  rintro ⟨w, c, a, k, p, h⟩ ⟨w', c', b, k', p', h'⟩ equal
  cases a <;> cases b <;> simp only [encodeFocus] at equal
  all_goals
    simp only [workFields, returnAtom, commonFields, List.cons_append, List.nil_append, packet_eq_iff,
      List.cons.injEq, and_true, HENativeOnTransform.atom_injective.eq_iff,
      code.world_injective.eq_iff, code.context_injective.eq_iff, HENativeOnTransform.stackField_injective.eq_iff,
      (HENativeOnTransform.parentsField_injective code).eq_iff, HENativeOnTransform.historyField_injective.eq_iff,
      HENativeOnTransform.answerField_injective.eq_iff, taskData_injective.eq_iff] at equal
  · rcases equal with ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, _⟩
    rfl
  · exact (workTag_not_return _ equal.1).elim
  · exact (workTag_not_return _ equal.1.symm).elim
  · rcases equal with ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl

/-- Which source boundaries the current compiled program covers. A
continuation that still owes other HE work is not declared terminal. -/
def Covered (state : Focus Context World) : Prop :=
  match state.leaf with
  | .work task =>
    (∃ request, NativeRequest.recognize task = some request) ∨
    (∃ request, HEContextEntry.Request.recognize task = some request) ∨
    (∃ request, HEAtomEntry.Request.recognize task = some request) ∨
    (∃ request, HEInvocationEntry.Request.recognize task = some request) ∨
    HEBodyEntry.covered task = true ∨ HEApplicationEntry.covered task = true ∨
    HEMinimalEntry.covered task = true ∨ HESnapshotEntry.covered task = true
  | .returning _ => True

theorem all_covered (state : Focus Context World) : Covered state := by
  rcases state with ⟨_, _, leaf, _, _, _⟩
  cases leaf with
  | returning => trivial
  | work task =>
    cases task <;> simp [Covered, HEBodyEntry.covered, HEApplicationEntry.covered,
      HEMinimalEntry.covered, HESnapshotEntry.covered, HEAtomEntry.Request.recognize,
      HEInvocationEntry.Request.recognize]

theorem covered_atom (request : HEAtomEntry.Request) (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) :
    Covered ⟨world, scope, .work request.task, stack, parents, emitted⟩ :=
  Or.inr (Or.inr (Or.inl ⟨request, HEAtomEntry.Request.recognize_task request⟩))

theorem covered_invocation (request : HEInvocationEntry.Request) (world : World) (scope : Context)
    (stack : List Continuation) (parents : List (Parent Context)) (emitted : List Result) :
    Covered ⟨world, scope, .work request.task, stack, parents, emitted⟩ :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨request, HEInvocationEntry.Request.recognize_task request⟩)))

theorem covered_body (task : Task) (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) (supported : HEBodyEntry.covered task = true) :
    Covered ⟨world, scope, .work task, stack, parents, emitted⟩ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl supported))))

theorem covered_application (task : Task) (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) (supported : HEApplicationEntry.covered task = true) :
    Covered ⟨world, scope, .work task, stack, parents, emitted⟩ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl supported)))))

theorem covered_return (frame : Continuation) (world : World) (scope : Context)
    (answers : List Result) (stack : List Continuation) (parents : List (Parent Context))
    (emitted : List Result) :
    Covered ⟨world, scope, .returning answers, frame :: stack, parents, emitted⟩ :=
  trivial

def applicationPort : Width → Nat
  | .direct => 18
  | .one => 19
  | .two => 20

def applicationRule (width : Width) : RuleWithCondition Nat Tm :=
  PureContinuationRules.rule (.schedule 9) (applicationPort width) width

def applicationRules : List (RuleWithCondition Nat Tm) := [applicationRule .direct, applicationRule .one, applicationRule .two]

private theorem application_rule_mem (width : Width) : applicationRule width ∈ applicationRules := by
  cases width <;> simp [applicationRules]

private theorem application_rule_origin {r : RuleWithCondition Nat Tm} (member : r ∈ applicationRules) :
    ∃ width, r = applicationRule width := by
  simp only [applicationRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same
  · exact ⟨.direct, same⟩
  · exact ⟨.one, same⟩
  · exact ⟨.two, same⟩

inductive PrimitiveFamily where
  | plain
  | bindings

def PrimitiveFamily.tag : PrimitiveFamily → Nat
  | .plain => 3
  | .bindings => 10

def PrimitiveFamily.port : PrimitiveFamily → Width → Nat
  | .plain, .direct => 21
  | .plain, .one => 22
  | .plain, .two => 23
  | .bindings, .direct => 24
  | .bindings, .one => 25
  | .bindings, .two => 26

def primitiveRule (family : PrimitiveFamily) (width : Width) : RuleWithCondition Nat Tm :=
  match family with
  | .plain => PureContinuationRules.rule (.schedule family.tag) (family.port width) width
  | .bindings => PureContinuationRules.worldRule (.work family.tag) (family.port width) width

def primitiveRules : List (RuleWithCondition Nat Tm) :=
  [primitiveRule .plain .direct, primitiveRule .plain .one,
    primitiveRule .bindings .direct, primitiveRule .bindings .one]

private theorem primitive_rule_mem (family : PrimitiveFamily) (width : Width)
    (bounded : width.slots.length ≤ 1) : primitiveRule family width ∈ primitiveRules := by
  cases family <;> cases width <;> simp_all [primitiveRules, Width.slots]

private theorem primitive_rule_origin {r : RuleWithCondition Nat Tm} (member : r ∈ primitiveRules) :
    ∃ family width, r = primitiveRule family width := by
  simp only [primitiveRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same
  · exact ⟨.plain, .direct, same⟩
  · exact ⟨.plain, .one, same⟩
  · exact ⟨.bindings, .direct, same⟩
  · exact ⟨.bindings, .one, same⟩

def PrimitiveFamily.plan (family : PrimitiveFamily) (env : WorldEnvironment Context World)
    (p : Policy) (w : World) (scope : Context) (task : Task)
    (next : World) (body : Leaf) (front : List Continuation) : Prop :=
  match family with
  | .plain => next = w ∧ HEMinimalEntry.Plan env.dispatch p task body front
  | .bindings => HESnapshotEntry.Plan env.services p w scope task next body front

private theorem primitive_bound (family : PrimitiveFamily) (env : WorldEnvironment Context World)
    (p : Policy) (w : World) (scope : Context) (task : Task) (next : World)
    (body : Leaf) (front : List Continuation)
    (planned : family.plan env p w scope task next body front) : front.length ≤ 1 := by
  cases family with
  | plain => exact planned.2.frames_bound
  | bindings => exact planned.frames_bound

def rules : List (RuleWithCondition Nat Tm) :=
  [HENativeOnTransform.rule, resumeRule, publishRule, HEContextOnTransform.enterRule, HEContextOnTransform.currentRule] ++
    HEAtomOnTransform.rules ++ HEInvocationOnTransform.rules ++
      HEBodyReturnOnTransform.bodyRules ++ HEBodyReturnOnTransform.returnRules ++ applicationRules ++ primitiveRules

private theorem rule_cases {r : RuleWithCondition Nat Tm} (within : r ∈ rules) :
    r = HENativeOnTransform.rule ∨ r = resumeRule ∨ r = publishRule ∨
      r = HEContextOnTransform.enterRule ∨ r = HEContextOnTransform.currentRule ∨
      r ∈ HEAtomOnTransform.rules ∨ r ∈ HEInvocationOnTransform.rules ∨
      r ∈ HEBodyReturnOnTransform.bodyRules ∨ r ∈ HEBodyReturnOnTransform.returnRules ∨
      r ∈ applicationRules ∨ r ∈ primitiveRules := by
  simpa only [rules, List.cons_append, List.nil_append, List.mem_cons, List.mem_append, or_assoc] using within

def operations (code : Presentation Context World) (environment : WorldEnvironment Context World)
    (policy : Policy) : Relations :=
  fun name args reply =>
    if name = 0 then HENativeOnTransform.operations code environment.services name args reply
    else if name < 3 then HEContextOnTransform.operations code environment.services policy name args reply
    else if name < 9 then HEAtomOnTransform.operations code environment policy name args reply
    else if name < 12 then HEInvocationOnTransform.operations code environment policy name args reply
    else if name < 18 then HEBodyReturnOnTransform.operations code environment policy name args reply
    else match name with
      | 18 => HEBodyReturnOnTransform.scheduleRead HEApplicationEntry.Plan .direct args reply
      | 19 => HEBodyReturnOnTransform.scheduleRead HEApplicationEntry.Plan .one args reply
      | 20 => HEBodyReturnOnTransform.scheduleRead HEApplicationEntry.Plan .two args reply
      | 21 => HEBodyReturnOnTransform.scheduleRead (HEMinimalEntry.Plan environment.dispatch policy) .direct args reply
      | 22 => HEBodyReturnOnTransform.scheduleRead (HEMinimalEntry.Plan environment.dispatch policy) .one args reply
      | 23 => HEBodyReturnOnTransform.scheduleRead (HEMinimalEntry.Plan environment.dispatch policy) .two args reply
      | 24 => HEBodyReturnOnTransform.worldRead code (HESnapshotEntry.Plan environment.services policy) .direct args reply
      | 25 => HEBodyReturnOnTransform.worldRead code (HESnapshotEntry.Plan environment.services policy) .one args reply
      | 26 => HEBodyReturnOnTransform.worldRead code (HESnapshotEntry.Plan environment.services policy) .two args reply
      | _ => False

private theorem native_port (code : Presentation Context World) (environment : WorldEnvironment Context World)
    (policy : Policy) (before after : Multiset Expr) :
    RelationStep (operations code environment policy) HENativeOnTransform.rule before after ↔
    RelationStep (HENativeOnTransform.operations code environment.services) HENativeOnTransform.rule before after := by
  apply StateRulesOnTheStep.operations_iff
  intro c member args reply
  rw [HENativeOnTransform.asks_native c member]
  simp [operations]

private theorem enter_port (code : Presentation Context World) (environment : WorldEnvironment Context World)
    (policy : Policy) (before after : Multiset Expr) :
    RelationStep (operations code environment policy) HEContextOnTransform.enterRule before after ↔
    RelationStep (HEContextOnTransform.operations code environment.services policy) HEContextOnTransform.enterRule before after := by
  apply StateRulesOnTheStep.operations_iff
  intro c member args reply
  rw [HEContextOnTransform.asks_enter c member]
  simp [operations]

private theorem current_port (code : Presentation Context World) (environment : WorldEnvironment Context World)
    (policy : Policy) (before after : Multiset Expr) :
    RelationStep (operations code environment policy) HEContextOnTransform.currentRule before after ↔
    RelationStep (HEContextOnTransform.operations code environment.services policy) HEContextOnTransform.currentRule before after := by
  apply StateRulesOnTheStep.operations_iff
  intro c member args reply
  rw [HEContextOnTransform.asks_current c member]
  simp [operations]

private theorem typed_port (code : Presentation Context World) (environment : WorldEnvironment Context World)
    (policy : Policy) (b : HEAtomOnTransform.Branch) (before after : Multiset Expr) :
    RelationStep (operations code environment policy) (HEAtomOnTransform.rule b) before after ↔
    RelationStep (HEAtomOnTransform.operations code environment policy) (HEAtomOnTransform.rule b) before after := by
  apply StateRulesOnTheStep.operations_iff
  intro c member args reply
  rw [HEAtomOnTransform.asks_port b c member]
  cases b <;> simp [operations, HEAtomOnTransform.Branch.port]

private theorem typed_input_tag {rel : Relations} {r : RuleWithCondition Nat Tm} {tag : Nat} {fields' : List Expr}
    {after : Multiset Expr} (inside : r ∈ HEAtomOnTransform.rules)
    (step : RelationStep rel r {packet tag fields'} after) : 6 = tag := by
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp inside
  exact HEAtomOnTransform.input_tag step

private theorem invocation_port (code : Presentation Context World) (environment : WorldEnvironment Context World)
    (policy : Policy) (s : HEInvocationOnTransform.Shape) (before after : Multiset Expr) :
    RelationStep (operations code environment policy) (HEInvocationOnTransform.rule s) before after ↔
    RelationStep (HEInvocationOnTransform.operations code environment policy) (HEInvocationOnTransform.rule s)
      before after := by
  apply StateRulesOnTheStep.operations_iff
  intro c member args reply
  rw [HEInvocationOnTransform.asks_port s c member]
  cases s <;> simp [operations, HEInvocationOnTransform.Shape.port]

private theorem invocation_input_tag {rel : Relations} {r : RuleWithCondition Nat Tm} {tag : Nat}
    {items : List Expr} {after : Multiset Expr} (inside : r ∈ HEInvocationOnTransform.rules)
    (step : RelationStep rel r {packet tag items} after) : 7 = tag := by
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp inside
  exact HEInvocationOnTransform.input_tag step

private theorem body_port (code : Presentation Context World) (environment : WorldEnvironment Context World)
    (policy : Policy) (width : Width) (before after : Multiset Expr) :
    RelationStep (operations code environment policy) (HEBodyReturnOnTransform.bodyRule width) before after ↔
    RelationStep (HEBodyReturnOnTransform.operations code environment policy)
      (HEBodyReturnOnTransform.bodyRule width) before after := by
  apply StateRulesOnTheStep.operations_iff
  intro c member args reply
  rw [PureContinuationRules.asks_port (.work 8) (HEBodyReturnOnTransform.bodyPort width) width c member]
  cases width <;> simp [operations, HEBodyReturnOnTransform.bodyPort]

private theorem return_port (code : Presentation Context World) (environment : WorldEnvironment Context World)
    (policy : Policy) (width : Width) (before after : Multiset Expr) :
    RelationStep (operations code environment policy) (HEBodyReturnOnTransform.returnRule width) before after ↔
    RelationStep (HEBodyReturnOnTransform.operations code environment policy)
      (HEBodyReturnOnTransform.returnRule width) before after := by
  apply StateRulesOnTheStep.operations_iff
  intro c member args reply
  rw [PureContinuationRules.asks_port .consume (HEBodyReturnOnTransform.returnPort width) width c member]
  cases width <;> simp [operations, HEBodyReturnOnTransform.returnPort]

private theorem body_input_tag {rel : Relations} {r : RuleWithCondition Nat Tm} {tag : Nat}
    {items : List Expr} {after : Multiset Expr} (inside : r ∈ HEBodyReturnOnTransform.bodyRules)
    (step : RelationStep rel r {packet tag items} after) : 8 = tag := by
  obtain ⟨width, rfl⟩ := HEBodyReturnOnTransform.body_rule_origin inside
  exact HEBodyReturnOnTransform.body_input_tag (width := width) step

private theorem return_input_tag {rel : Relations} {r : RuleWithCondition Nat Tm} {tag : Nat}
    {items : List Expr} {after : Multiset Expr} (inside : r ∈ HEBodyReturnOnTransform.returnRules)
    (step : RelationStep rel r {packet tag items} after) : 2 = tag := by
  obtain ⟨width, rfl⟩ := HEBodyReturnOnTransform.return_rule_origin inside
  exact HEBodyReturnOnTransform.return_input_tag (width := width) step

private theorem application_input_tag {rel : Relations} {r : RuleWithCondition Nat Tm} {tag : Nat}
    {items : List Expr} {after : Multiset Expr} (inside : r ∈ applicationRules)
    (step : RelationStep rel r {packet tag items} after) : 9 = tag := by
  obtain ⟨width, rfl⟩ := application_rule_origin inside
  exact PureContinuationRules.input_tag (mode := .schedule 9) (port := applicationPort width) (width := width) step

private theorem primitive_rule_tag {rel : Relations} {family : PrimitiveFamily} {width : Width}
    {tag : Nat} {items : List Expr} {after : Multiset Expr}
    (step : RelationStep rel (primitiveRule family width) {packet tag items} after) : family.tag = tag := by
  cases family with
  | plain => exact PureContinuationRules.input_tag (mode := .schedule 3) (port := PrimitiveFamily.port .plain width) step
  | bindings =>
    exact PureContinuationRules.world_input_tag (mode := .work 10) (port := PrimitiveFamily.port .bindings width) step

private theorem primitive_input_tag {rel : Relations} {r : RuleWithCondition Nat Tm} {tag : Nat}
    {items : List Expr} {after : Multiset Expr} (inside : r ∈ primitiveRules)
    (step : RelationStep rel r {packet tag items} after) : 3 = tag ∨ 10 = tag := by
  obtain ⟨family, width, rfl⟩ := primitive_rule_origin inside
  cases family with
  | plain => exact Or.inl (primitive_rule_tag (family := .plain) (width := width) step)
  | bindings => exact Or.inr (primitive_rule_tag (family := .bindings) (width := width) step)

theorem ordinary_firing_tag {rel : Relations} {r : RuleWithCondition Nat Tm} {tag : Nat}
    {items : List Expr} {after : Multiset Expr} (listed : r ∈ rules)
    (fires : RelationStep rel r {packet tag items} after) : tag < 11 := by
  rcases rule_cases listed with rfl | rfl | rfl | rfl | rfl | typed | queried | bodies | returns | application | primitive
  · have equal := HENativeOnTransform.input_tag fires; omega
  · have equal := resume_tag fires; omega
  · have equal := publish_tag fires; omega
  · have equal := HEContextOnTransform.enters_only_tag fires; omega
  · have equal := HEContextOnTransform.current_only_tag fires; omega
  · have equal := typed_input_tag typed fires; omega
  · have equal := invocation_input_tag queried fires; omega
  · have equal := body_input_tag bodies fires; omega
  · have equal := return_input_tag returns fires; omega
  · have equal := application_input_tag application fires; omega
  · rcases primitive_input_tag primitive fires with equal | equal <;> omega

theorem encoded_ordinary_tag (code : Presentation Context World) (state : Focus Context World) :
    ∃ tag < 11, ∃ fields, encodeFocus code state = packet tag fields := by
  rcases state with ⟨world, scope, leaf, stack, parents, emitted⟩
  cases leaf with
  | returning => exact ⟨2, by decide, _, rfl⟩
  | work task =>
    refine ⟨(workView task).1, ?_, _, rfl⟩
    have normal : ∀ task, ordinaryTag task < 11 := by
      intro pending
      cases pending <;> simp [ordinaryTag, HESnapshotEntry.covered]
      case minimal live scope caller value frame =>
        by_cases kind : HESnapshotEntry.isInstruction value = true <;> simp [kind]
    cases native : NativeRequest.recognize task with
    | some request => simp [workView, native]
    | none =>
      cases context : HEContextEntry.Request.recognize task with
      | none => simpa only [workView, native, context] using normal task
      | some request =>
        simp only [workView, native, context]
        cases form : request.instruction <;> simp [HEContextOnTransform.requestTag, form]

/-- The original program's relation names are disjoint from the two
relations of an explicit equational entry. -/
theorem ordinary_port {r : RuleWithCondition Nat Tm} (listed : r ∈ rules)
    (c : Condition Nat Tm) (present : c ∈ r.conditions) : c.name < 27 := by
  rcases rule_cases listed with rfl | rfl | rfl | rfl | rfl | typed | queried | bodies | returns | application | primitive
  · rw [HENativeOnTransform.asks_native c present]; decide
  · cases present
  · cases present
  · rw [HEContextOnTransform.asks_enter c present]; decide
  · rw [HEContextOnTransform.asks_current c present]; decide
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp typed
    rw [HEAtomOnTransform.asks_port b c present]
    cases b <;> decide
  · obtain ⟨s, _, rfl⟩ := List.mem_map.mp queried
    rw [HEInvocationOnTransform.asks_port s c present]
    cases s <;> decide
  · obtain ⟨w, rfl⟩ := HEBodyReturnOnTransform.body_rule_origin bodies
    rw [PureContinuationRules.asks_port (.work 8) (HEBodyReturnOnTransform.bodyPort w) w c present]
    cases w <;> decide
  · obtain ⟨w, rfl⟩ := HEBodyReturnOnTransform.return_rule_origin returns
    rw [PureContinuationRules.asks_port .consume (HEBodyReturnOnTransform.returnPort w) w c present]
    cases w <;> decide
  · obtain ⟨w, rfl⟩ := application_rule_origin application
    rw [PureContinuationRules.asks_port (.schedule 9) (applicationPort w) w c present]
    cases w <;> decide
  · obtain ⟨k, w, rfl⟩ := primitive_rule_origin primitive
    cases k with
    | plain =>
      rw [PureContinuationRules.asks_port (.schedule 3) (PrimitiveFamily.port .plain w) w c present]
      cases w <;> decide
    | bindings =>
      rw [PureContinuationRules.world_asks_port (.work 10) (PrimitiveFamily.port .bindings w) w c present]
      cases w <;> decide

section Execution

variable (environment : WorldEnvironment Context World) (policy : Policy)

private theorem scope_rules_exact (code : Presentation Context World) (request : HEContextEntry.Request)
    (world : World) (scope : Context) (stack : List Continuation) (parents : List (Parent Context))
    (emitted : List Result) (after : Multiset Expr) :
    (∃ r ∈ rules, RelationStep (operations code environment policy) r
      {HEContextOnTransform.requestAtom code request world scope stack parents emitted} after) ↔
    ∃ next, HEContextEntry.Resulting environment.services policy request world scope stack parents emitted next ∧
      after = {encodeFocus code next} := by
  constructor
  · rintro ⟨r, listed, fires⟩
    rcases rule_cases listed with rfl | rfl | rfl | rfl | rfl | typed | queried | body | returns | application | primitive
    · exact ((HEContextOnTransform.tag_not_native request) (HENativeOnTransform.input_tag fires).symm).elim
    · exact ((HEContextOnTransform.tag_not_return request) (resume_tag fires).symm).elim
    · exact ((HEContextOnTransform.tag_not_return request) (publish_tag fires).symm).elim
    · obtain ⟨handle, task, child, prepared, named, made⟩ := (HEContextOnTransform.enter_exact
        code environment.services policy request world scope stack parents emitted after).mp
          ((enter_port code environment policy _ _).mp fires)
      have ordinary := HEContextOnTransform.child_is_ordinary policy prepared
      refine ⟨⟨world, child, .work task, [], ⟨scope, stack⟩ :: parents, emitted⟩, ?_, ?_⟩
      · rw [HEContextEntry.Resulting, prepared]
        exact ⟨child, named, rfl⟩
      · rw [encode_ordinary code _ _ _ _ _ _ ordinary.1 ordinary.2]
        exact made
    · obtain ⟨read, made⟩ := (HEContextOnTransform.current_exact
        code environment.services policy request world scope stack parents emitted after).mp
          ((current_port code environment policy _ _).mp fires)
      refine ⟨⟨world, scope, .returning [(.grounded (environment.services.contextPayload scope), request.frame)],
        stack, parents, emitted⟩, ?_, made⟩
      rw [HEContextEntry.Resulting, read]
    · exact ((HEContextOnTransform.tag_not_typed request) (typed_input_tag typed fires).symm).elim
    · exact ((HEContextOnTransform.tag_not_invocation request) (invocation_input_tag queried fires).symm).elim
    · exact ((HEContextOnTransform.tag_not_body request) (body_input_tag body fires).symm).elim
    · exact ((HEContextOnTransform.tag_not_return request) (return_input_tag returns fires).symm).elim
    · exact ((HEContextOnTransform.tag_not_application request) (application_input_tag application fires).symm).elim
    · rcases primitive_input_tag primitive fires with ordinary | snapshot
      · exact ((HEContextOnTransform.tag_not_ordinary request) ordinary.symm).elim
      · exact ((HEContextOnTransform.tag_not_snapshot request) snapshot.symm).elim
  · rintro ⟨next, completes, result⟩
    cases prepared : request.childTask policy with
    | none =>
      simp only [HEContextEntry.Resulting, prepared] at completes
      subst next
      refine ⟨HEContextOnTransform.currentRule, by simp [rules], (current_port code environment policy _ _).mpr ?_⟩
      exact (HEContextOnTransform.current_exact code environment.services policy request world scope stack parents
        emitted after).mpr ⟨prepared, result⟩
    | some task =>
      rcases task with ⟨handle, body⟩
      simp only [HEContextEntry.Resulting, prepared] at completes
      obtain ⟨child, named, rfl⟩ := completes
      have ordinary := HEContextOnTransform.child_is_ordinary policy prepared
      rw [encode_ordinary code _ _ _ _ _ _ ordinary.1 ordinary.2] at result
      refine ⟨HEContextOnTransform.enterRule, by simp [rules], (enter_port code environment policy _ _).mpr ?_⟩
      exact (HEContextOnTransform.enter_exact code environment.services policy request world scope stack parents
        emitted after).mpr ⟨handle, body, child, prepared, named, result⟩

private theorem typed_outcome (code : Presentation Context World) (request : HEAtomEntry.Request)
    (reply : HEAtomEntry.Reply) (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) :
    HEAtomOnTransform.outcomeAtom code policy request reply world scope stack parents emitted =
      encodeFocus code ⟨world, scope, (HEAtomEntry.continuation policy request reply).1,
        (HEAtomEntry.continuation policy request reply).2 ++ stack, parents, emitted⟩ := by
  rw [HEAtomOnTransform.outcome_shape]
  cases target : (HEAtomEntry.continuation policy request reply).1 with
  | returning answers => rfl
  | work body =>
    have ordinary := HEAtomOnTransform.work_outcome_is_ordinary policy request reply target
    exact (encode_ordinary code _ _ _ _ _ _ ordinary.1 ordinary.2.1).symm

private theorem typed_rules_exact (code : Presentation Context World) (request : HEAtomEntry.Request)
    (world : World) (scope : Context) (stack : List Continuation) (parents : List (Parent Context))
    (emitted : List Result) (after : Multiset Expr) :
    (∃ r ∈ rules, RelationStep (operations code environment policy) r
      {HEAtomOnTransform.requestAtom code request world scope stack parents emitted} after) ↔
    ∃ next, HEFocused.Move environment.arguments environment.view environment.services environment.dispatch
      environment.lookup policy ⟨world, scope, .work request.task, stack, parents, emitted⟩ next ∧
      after = {encodeFocus code next} := by
  constructor
  · rintro ⟨r, listed, fires⟩
    rcases rule_cases listed with rfl | rfl | rfl | rfl | rfl | typed | queried | body | returns | application | primitive
    · exact (by have bad := HENativeOnTransform.input_tag fires; cases bad)
    · exact (by have bad := resume_tag fires; cases bad)
    · exact (by have bad := publish_tag fires; cases bad)
    · exact (by have bad := HEContextOnTransform.enters_only_tag fires; cases bad)
    · exact (by have bad := HEContextOnTransform.current_only_tag fires; cases bad)
    · obtain ⟨branch, _, rfl⟩ := List.mem_map.mp typed
      obtain ⟨reply, _, allowed, produced⟩ := (HEAtomOnTransform.rule_exact code environment policy branch request
        world scope stack parents emitted after).mp ((typed_port code environment policy branch _ _).mp fires)
      exact ⟨_, (HEAtomEntry.step_iff environment policy request world scope stack parents emitted _).mpr
        ⟨reply, allowed, rfl⟩, produced.trans (congrArg (fun term => ({term} : Multiset Expr))
          (typed_outcome policy code request reply world scope stack parents emitted))⟩
    · exact (by have bad := invocation_input_tag queried fires; cases bad)
    · exact (by have bad := body_input_tag body fires; cases bad)
    · exact (by have bad := return_input_tag returns fires; cases bad)
    · exact (by have bad := application_input_tag application fires; cases bad)
    · rcases primitive_input_tag primitive fires with bad | bad <;> cases bad
  · rintro ⟨next, stepped, produced⟩
    obtain ⟨reply, allowed, rfl⟩ := (HEAtomEntry.step_iff environment policy request world scope stack parents
      emitted next).mp stepped
    let branch := HEAtomOnTransform.branchOf reply
    have within : HEAtomOnTransform.rule branch ∈ HEAtomOnTransform.rules :=
      List.mem_map_of_mem (HEAtomOnTransform.branch_mem branch)
    refine ⟨HEAtomOnTransform.rule branch, by simp [rules, within],
      (typed_port code environment policy branch _ _).mpr ?_⟩
    exact (HEAtomOnTransform.rule_exact code environment policy branch request world scope stack parents
      emitted after).mpr ⟨reply, rfl, allowed, produced.trans (congrArg (fun term => ({term} : Multiset Expr))
        (typed_outcome policy code request reply world scope stack parents emitted).symm)⟩

private theorem invocation_outcome (code : Presentation Context World) (world : World) (scope : Context)
    (body : Leaf) (frames stack : List Continuation) (parents : List (Parent Context)) (emitted : List Result) :
    HEInvocationOnTransform.outcomeAtom code world scope body frames stack parents emitted =
      encodeFocus code ⟨world, scope, body, frames ++ stack, parents, emitted⟩ := by
  cases body <;> rfl

private theorem invocation_rules_exact (code : Presentation Context World) (reward : HEInvocationEntry.Request)
    (world : World) (scope : Context) (stack : List Continuation) (parents : List (Parent Context))
    (emitted : List Result) (after : Multiset Expr) :
    (∃ r ∈ rules, RelationStep (operations code environment policy) r
      {HEInvocationOnTransform.requestAtom code reward world scope stack parents emitted} after) ↔
    ∃ next, HEFocused.Move environment.arguments environment.view environment.services environment.dispatch
      environment.lookup policy ⟨world, scope, .work reward.task, stack, parents, emitted⟩ next ∧
      after = {encodeFocus code next} := by
  constructor
  · rintro ⟨r, listed, fires⟩
    rcases rule_cases listed with rfl | rfl | rfl | rfl | rfl | typed | queried | bodyRules | returns | application | primitive
    · exact (by have bad := HENativeOnTransform.input_tag fires; cases bad)
    · exact (by have bad := resume_tag fires; cases bad)
    · exact (by have bad := publish_tag fires; cases bad)
    · exact (by have bad := HEContextOnTransform.enters_only_tag fires; cases bad)
    · exact (by have bad := HEContextOnTransform.current_only_tag fires; cases bad)
    · exact (by have bad := typed_input_tag typed fires; cases bad)
    · obtain ⟨shape, _, rfl⟩ := List.mem_map.mp queried
      obtain ⟨reply, next, body, frames, allowed, planned, _, result⟩ :=
        (HEInvocationOnTransform.rule_exact code environment policy shape reward world scope stack parents emitted
          after).mp ((invocation_port code environment policy shape _ _).mp fires)
      exact ⟨_, (HEInvocationEntry.step_iff environment policy reward world scope stack parents emitted _).mpr
        ⟨reply, next, body, frames, allowed, planned, rfl⟩, result.trans (congrArg (fun term => ({term} : Multiset Expr))
          (invocation_outcome code next scope body frames stack parents emitted))⟩
    · exact (by have bad := body_input_tag bodyRules fires; cases bad)
    · exact (by have bad := return_input_tag returns fires; cases bad)
    · exact (by have bad := application_input_tag application fires; cases bad)
    · rcases primitive_input_tag primitive fires with bad | bad <;> cases bad
  · rintro ⟨next, stepped, result⟩
    obtain ⟨reply, afterWorld, body, frames, allowed, planned, rfl⟩ :=
      (HEInvocationEntry.step_iff environment policy reward world scope stack parents emitted next).mp stepped
    have bounded := HEInvocationEntry.frames_bounded policy environment.dispatch reward reply body frames planned
    obtain ⟨shape, width⟩ := HEInvocationOnTransform.shape_of_length bounded
    have within : HEInvocationOnTransform.rule shape ∈ HEInvocationOnTransform.rules :=
      List.mem_map_of_mem (HEInvocationOnTransform.shape_mem shape)
    refine ⟨HEInvocationOnTransform.rule shape, by simp [rules, within],
      (invocation_port code environment policy shape _ _).mpr ?_⟩
    exact (HEInvocationOnTransform.rule_exact code environment policy shape reward world scope stack parents
      emitted after).mpr ⟨reply, afterWorld, body, frames, allowed, planned, width,
        result.trans (congrArg (fun term => ({term} : Multiset Expr))
          (invocation_outcome code afterWorld scope body frames stack parents emitted).symm)⟩

private theorem continuation_outcome (code : Presentation Context World) (world : World) (scope : Context)
    (body : Leaf) (frames stack : List Continuation) (parents : List (Parent Context)) (emitted : List Result) :
    HEBodyReturnOnTransform.outcomeAtom code world scope body frames stack parents emitted =
      encodeFocus code ⟨world, scope, body, frames ++ stack, parents, emitted⟩ := by
  cases body <;> rfl

private theorem body_rules_exact (code : Presentation Context World) (task : Task)
    (world : World) (scope : Context) (stack : List Continuation) (parents : List (Parent Context))
    (emitted : List Result) (after : Multiset Expr) :
    (∃ r ∈ rules, RelationStep (operations code environment policy) r
      {HEBodyReturnOnTransform.requestAtom code task world scope stack parents emitted} after) ↔
    ∃ next, HEBodyEntry.covered task = true ∧
      HEFocused.Move environment.arguments environment.view environment.services environment.dispatch
        environment.lookup policy ⟨world, scope, .work task, stack, parents, emitted⟩ next ∧
      after = {encodeFocus code next} := by
  constructor
  · rintro ⟨r, listed, fires⟩
    rcases rule_cases listed with rfl | rfl | rfl | rfl | rfl | typed | queried | bodies | returns | application | primitive
    · exact (by have bad := HENativeOnTransform.input_tag fires; cases bad)
    · exact (by have bad := resume_tag fires; cases bad)
    · exact (by have bad := publish_tag fires; cases bad)
    · exact (by have bad := HEContextOnTransform.enters_only_tag fires; cases bad)
    · exact (by have bad := HEContextOnTransform.current_only_tag fires; cases bad)
    · exact (by have bad := typed_input_tag typed fires; cases bad)
    · exact (by have bad := invocation_input_tag queried fires; cases bad)
    · obtain ⟨width, rfl⟩ := HEBodyReturnOnTransform.body_rule_origin bodies
      obtain ⟨body, frames, planned, _, result⟩ := (HEBodyReturnOnTransform.body_exact code environment policy
        width task world scope stack parents emitted after).mp ((body_port code environment policy width _ _).mp fires)
      exact ⟨_, planned.covered, (HEBodyEntry.step_iff environment policy task planned.covered
        world scope stack parents emitted _).mpr ⟨body, frames, planned, rfl⟩,
        result.trans (congrArg (fun term => ({term} : Multiset Expr))
          (continuation_outcome code world scope body frames stack parents emitted))⟩
    · exact (by have bad := return_input_tag returns fires; cases bad)
    · exact (by have bad := application_input_tag application fires; cases bad)
    · rcases primitive_input_tag primitive fires with bad | bad <;> cases bad
  · rintro ⟨next, supported, stepped, result⟩
    obtain ⟨body, frames, planned, rfl⟩ :=
      (HEBodyEntry.step_iff environment policy task supported world scope stack parents emitted next).mp stepped
    obtain ⟨width, count⟩ := PureContinuationRules.width_of_length planned.frames_bound
    have within := HEBodyReturnOnTransform.body_rule_mem width (count ▸ planned.frames_bound)
    refine ⟨_, by simp [rules, within], (body_port code environment policy width _ _).mpr ?_⟩
    exact (HEBodyReturnOnTransform.body_exact code environment policy width task world scope stack parents
      emitted after).mpr ⟨body, frames, planned, count, result.trans
        (congrArg (fun term => ({term} : Multiset Expr))
          (continuation_outcome code world scope body frames stack parents emitted).symm)⟩

private theorem return_rules_exact (code : Presentation Context World) (frame : Continuation) (answers : List Result)
    (world : World) (scope : Context) (stack : List Continuation) (parents : List (Parent Context))
    (emitted : List Result) (after : Multiset Expr) :
    (∃ r ∈ rules, RelationStep (operations code environment policy) r
      {returnAtom code world scope answers (frame :: stack) parents emitted} after) ↔
    ∃ next, Covered ⟨world, scope, .returning answers, frame :: stack, parents, emitted⟩ ∧
      HEFocused.Move environment.arguments environment.view environment.services environment.dispatch
        environment.lookup policy ⟨world, scope, .returning answers, frame :: stack, parents, emitted⟩ next ∧
      after = {encodeFocus code next} := by
  constructor
  · rintro ⟨r, listed, fires⟩
    rcases rule_cases listed with rfl | rfl | rfl | rfl | rfl | typed | queried | bodies | returns | application | primitive
    · exact (by have bad := HENativeOnTransform.input_tag fires; cases bad)
    · obtain ⟨_, _, bad, _, _⟩ := (resume_rewrite_iff code _ _ _ _ _ _ _ _).mp fires
      cases bad
    · obtain ⟨_, _, bad, _, _, _⟩ := (publish_rewrite_iff code _ _ _ _ _ _ _ _).mp fires
      cases bad
    · exact (by have bad := HEContextOnTransform.enters_only_tag fires; cases bad)
    · exact (by have bad := HEContextOnTransform.current_only_tag fires; cases bad)
    · exact (by have bad := typed_input_tag typed fires; cases bad)
    · exact (by have bad := invocation_input_tag queried fires; cases bad)
    · exact (by have bad := body_input_tag bodies fires; cases bad)
    · obtain ⟨width, rfl⟩ := HEBodyReturnOnTransform.return_rule_origin returns
      obtain ⟨body, frames, planned, _, result⟩ := (HEBodyReturnOnTransform.return_exact code environment policy
        width frame answers world scope stack parents emitted after).mp
          ((return_port code environment policy width _ _).mp fires)
      exact ⟨_, trivial, (HESnapshotEntry.return_iff environment policy frame answers
        world scope stack parents emitted _).mpr ⟨body, frames, planned, rfl⟩,
        result.trans (congrArg (fun term => ({term} : Multiset Expr))
          (continuation_outcome code world scope body frames stack parents emitted))⟩
    · exact (by have bad := application_input_tag application fires; cases bad)
    · rcases primitive_input_tag primitive fires with bad | bad <;> cases bad
  · rintro ⟨next, _, stepped, result⟩
    obtain ⟨body, frames, planned, rfl⟩ :=
      (HESnapshotEntry.return_iff environment policy frame answers world scope stack parents emitted next).mp stepped
    obtain ⟨width, count⟩ := PureContinuationRules.width_of_length planned.frames_bound
    have within := HEBodyReturnOnTransform.return_rule_mem width (count ▸ planned.frames_bound)
    refine ⟨_, by simp [rules, within], (return_port code environment policy width _ _).mpr ?_⟩
    exact (HEBodyReturnOnTransform.return_exact code environment policy width frame answers world scope stack parents
      emitted after).mpr ⟨body, frames, planned, count, result.trans
        (congrArg (fun term => ({term} : Multiset Expr))
          (continuation_outcome code world scope body frames stack parents emitted).symm)⟩

private theorem application_rules_exact (code : Presentation Context World) (task : Task)
    (world : World) (scope : Context) (stack : List Continuation) (parents : List (Parent Context))
    (emitted : List Result) (after : Multiset Expr) :
    (∃ r ∈ rules, RelationStep (operations code environment policy) r
      {packet 9 (workFields code task world scope stack parents emitted)} after) ↔
    ∃ next, HEApplicationEntry.covered task = true ∧
      HEFocused.Move environment.arguments environment.view environment.services environment.dispatch
        environment.lookup policy ⟨world, scope, .work task, stack, parents, emitted⟩ next ∧
      after = {encodeFocus code next} := by
  have exactRule (width : Width) :
      RelationStep (operations code environment policy) (applicationRule width)
        {packet 9 (workFields code task world scope stack parents emitted)} after ↔
      ∃ body frames, HEApplicationEntry.Plan task body frames ∧ frames.length = width.slots.length ∧
        after = {HEBodyReturnOnTransform.outcomeAtom code world scope body frames stack parents emitted} :=
    HEBodyReturnOnTransform.schedule_exact code HEApplicationEntry.Plan 9 (applicationPort width) width
      (operations code environment policy) (by cases width <;> intros <;> simp [operations, applicationPort])
      task world scope stack parents emitted after
  constructor
  · rintro ⟨r, listed, fires⟩
    rcases rule_cases listed with rfl | rfl | rfl | rfl | rfl | typed | queried | bodies | returns | application | primitive
    · exact (by have bad := HENativeOnTransform.input_tag fires; cases bad)
    · exact (by have bad := resume_tag fires; cases bad)
    · exact (by have bad := publish_tag fires; cases bad)
    · exact (by have bad := HEContextOnTransform.enters_only_tag fires; cases bad)
    · exact (by have bad := HEContextOnTransform.current_only_tag fires; cases bad)
    · exact (by have bad := typed_input_tag typed fires; cases bad)
    · exact (by have bad := invocation_input_tag queried fires; cases bad)
    · exact (by have bad := body_input_tag bodies fires; cases bad)
    · exact (by have bad := return_input_tag returns fires; cases bad)
    · obtain ⟨width, rfl⟩ := application_rule_origin application
      obtain ⟨body, frames, planned, _, result⟩ := (exactRule width).mp fires
      exact ⟨_, planned.covered, (HEApplicationEntry.step_iff environment policy task planned.covered
        world scope stack parents emitted _).mpr ⟨body, frames, planned, rfl⟩,
        result.trans (congrArg (fun term => ({term} : Multiset Expr))
          (continuation_outcome code world scope body frames stack parents emitted))⟩
    · rcases primitive_input_tag primitive fires with bad | bad <;> cases bad
  · rintro ⟨next, supported, stepped, result⟩
    obtain ⟨body, frames, planned, rfl⟩ :=
      (HEApplicationEntry.step_iff environment policy task supported world scope stack parents emitted next).mp stepped
    obtain ⟨width, count⟩ := PureContinuationRules.width_of_length_le_two planned.frames_bound
    have within := application_rule_mem width
    refine ⟨_, by simp [rules, within], (exactRule width).mpr ⟨body, frames, planned, count, ?_⟩⟩
    exact result.trans (congrArg (fun term => ({term} : Multiset Expr))
      (continuation_outcome code world scope body frames stack parents emitted).symm)

private theorem primitive_rules_exact (code : Presentation Context World) (family : PrimitiveFamily) (task : Task)
    (world : World) (scope : Context) (stack : List Continuation) (parents : List (Parent Context))
    (emitted : List Result) (after : Multiset Expr) :
    (∃ r ∈ rules, RelationStep (operations code environment policy) r
      {packet family.tag (workFields code task world scope stack parents emitted)} after) ↔
    ∃ next body front, family.plan environment policy world scope task next body front ∧
      after = {encodeFocus code ⟨next, scope, body, front ++ stack, parents, emitted⟩} := by
  have exactRule (width : Width) :
      RelationStep (operations code environment policy) (primitiveRule family width)
        {packet family.tag (workFields code task world scope stack parents emitted)} after ↔
      ∃ next body front, family.plan environment policy world scope task next body front ∧
        front.length = width.slots.length ∧
        after = {HEBodyReturnOnTransform.outcomeAtom code next scope body front stack parents emitted} := by
    cases family with
    | plain =>
      have compiled := HEBodyReturnOnTransform.schedule_exact code (HEMinimalEntry.Plan environment.dispatch policy)
        3 (PrimitiveFamily.port .plain width) width (operations code environment policy)
        (by cases width <;> intros <;> simp [operations, PrimitiveFamily.port])
        task world scope stack parents emitted after
      constructor
      · intro fires
        obtain ⟨body, front, plan, count, result⟩ := compiled.mp fires
        exact ⟨world, body, front, ⟨rfl, plan⟩, count, result⟩
      · rintro ⟨next, body, front, planned, count, result⟩
        obtain ⟨rfl, plan⟩ := planned
        exact compiled.mpr ⟨body, front, plan, count, result⟩
    | bindings =>
      exact HEBodyReturnOnTransform.world_schedule_exact code (HESnapshotEntry.Plan environment.services policy)
        10 (PrimitiveFamily.port .bindings width) width (operations code environment policy)
        (by cases width <;> intros <;> simp [operations, PrimitiveFamily.port])
        task world scope stack parents emitted after
  constructor
  · rintro ⟨r, listed, fires⟩
    rcases rule_cases listed with rfl | rfl | rfl | rfl | rfl | typed | queried | bodies | returns | application | primitive
    · have bad := HENativeOnTransform.input_tag fires
      cases family <;> cases bad
    · have bad := resume_tag fires
      cases family <;> cases bad
    · have bad := publish_tag fires
      cases family <;> cases bad
    · have bad := HEContextOnTransform.enters_only_tag fires
      cases family <;> cases bad
    · have bad := HEContextOnTransform.current_only_tag fires
      cases family <;> cases bad
    · have bad := typed_input_tag typed fires
      cases family <;> cases bad
    · have bad := invocation_input_tag queried fires
      cases family <;> cases bad
    · have bad := body_input_tag bodies fires
      cases family <;> cases bad
    · have bad := return_input_tag returns fires
      cases family <;> cases bad
    · have bad := application_input_tag application fires
      cases family <;> cases bad
    · obtain ⟨actual, width, rfl⟩ := primitive_rule_origin primitive
      have same := primitive_rule_tag (family := actual) (width := width) fires
      obtain rfl : actual = family := by cases actual <;> cases family <;> first | rfl | cases same
      obtain ⟨next, body, front, planned, _, result⟩ := (exactRule width).mp fires
      exact ⟨next, body, front, planned, result.trans (congrArg (fun term => ({term} : Multiset Expr))
        (continuation_outcome code next scope body front stack parents emitted))⟩
  · rintro ⟨next, body, front, planned, result⟩
    have bound := primitive_bound family environment policy world scope task next body front planned
    obtain ⟨width, count⟩ := PureContinuationRules.width_of_length bound
    have within := primitive_rule_mem family width (count ▸ bound)
    refine ⟨_, by simp [rules, within], (exactRule width).mpr ⟨next, body, front, planned, count, ?_⟩⟩
    exact result.trans (congrArg (fun term => ({term} : Multiset Expr))
      (continuation_outcome code next scope body front stack parents emitted).symm)

/-- Every firing reads back in the
original live source relation. The rule tags separate work and returns;
return and publication in turn distinguish the saved parent. -/
theorem relation_step_iff (code : Presentation Context World)
    (before : Focus Context World) (after : Multiset Expr) :
    (∃ r ∈ rules, RelationStep (operations code environment policy) r {encodeFocus code before} after) ↔
      ∃ next, Covered before ∧ HEFocused.Move environment.arguments environment.view environment.services
        environment.dispatch environment.lookup policy before next ∧ after = {encodeFocus code next} := by
  rcases before with ⟨world, scope, leaf, stack, parents, emitted⟩
  cases leaf with
  | work task =>
    cases recognized : NativeRequest.recognize task with
    | none =>
      cases scopeRecognized : HEContextEntry.Request.recognize task with
      | none =>
        cases typedRecognized : HEAtomEntry.Request.recognize task with
        | none =>
          cases invocationRecognized : HEInvocationEntry.Request.recognize task with
          | none =>
            cases supported : HEBodyEntry.covered task with
            | true =>
              rw [encode_body code task world scope stack parents emitted supported, body_rules_exact environment policy]
              constructor
              · rintro ⟨next, allowed, move, produced⟩
                exact ⟨next, covered_body task world scope stack parents emitted allowed, move, produced⟩
              · rintro ⟨next, _, move, produced⟩
                exact ⟨next, supported, move, produced⟩
            | false =>
              cases schedules : HEApplicationEntry.covered task with
              | true =>
                rw [encode_application code task world scope stack parents emitted schedules,
                  application_rules_exact environment policy]
                constructor
                · rintro ⟨next, allowed, move, produced⟩
                  exact ⟨next, covered_application task world scope stack parents emitted allowed, move, produced⟩
                · rintro ⟨next, _, move, produced⟩
                  exact ⟨next, schedules, move, produced⟩
              | false =>
                cases snapshots : HESnapshotEntry.covered task with
                | true =>
                  have tag : ordinaryTag task = PrimitiveFamily.bindings.tag := by
                    cases task <;> simp_all [ordinaryTag, HESnapshotEntry.covered, PrimitiveFamily.tag]
                  rw [encode_ordinary code _ _ _ _ _ _ recognized scopeRecognized, ordinaryAtom, tag,
                    primitive_rules_exact environment policy]
                  constructor
                  · rintro ⟨next, body, front, plan, result⟩
                    exact ⟨_, all_covered _, (HESnapshotEntry.step_iff environment policy task snapshots world scope
                      stack parents emitted _).mpr ⟨next, body, front, plan, rfl⟩, result⟩
                  · rintro ⟨next, _, moved, result⟩
                    obtain ⟨world', body, front, plan, rfl⟩ := (HESnapshotEntry.step_iff environment policy task
                      snapshots world scope stack parents emitted next).mp moved
                    exact ⟨world', body, front, plan, result⟩
                | false =>
                  have localOnly : HEMinimalEntry.covered task = true := by
                    cases task <;> simp_all [HEAtomEntry.Request.recognize, HEInvocationEntry.Request.recognize,
                      HEBodyEntry.covered, HEApplicationEntry.covered, HESnapshotEntry.covered, HEMinimalEntry.covered]
                  have tag : ordinaryTag task = PrimitiveFamily.plain.tag := by
                    cases task <;> simp_all [ordinaryTag, HEMinimalEntry.covered, HESnapshotEntry.covered, PrimitiveFamily.tag]
                  rw [encode_ordinary code _ _ _ _ _ _ recognized scopeRecognized, ordinaryAtom, tag,
                    primitive_rules_exact environment policy]
                  have localStep := HEMinimalEntry.step_iff environment policy task localOnly recognized scopeRecognized
                    snapshots world scope stack parents emitted
                  constructor
                  · rintro ⟨next, body, front, plan, result⟩
                    obtain ⟨rfl, planned⟩ := plan
                    exact ⟨_, all_covered _, (localStep _).mpr ⟨body, front, planned, rfl⟩, result⟩
                  · rintro ⟨next, _, moved, result⟩
                    obtain ⟨body, front, planned, rfl⟩ := (localStep next).mp moved
                    exact ⟨world, body, front, ⟨rfl, planned⟩, result⟩
          | some request =>
            have same := HEInvocationEntry.Request.recognize_exact invocationRecognized
            subst task
            rw [encode_invocation, invocation_rules_exact environment policy]
            constructor
            · rintro ⟨next, move, produced⟩
              exact ⟨next, covered_invocation request world scope stack parents emitted, move, produced⟩
            · rintro ⟨next, _, move, produced⟩
              exact ⟨next, move, produced⟩
        | some request =>
          have same := HEAtomEntry.Request.recognize_exact typedRecognized
          subst task
          rw [encode_atom, typed_rules_exact environment policy]
          constructor
          · rintro ⟨next, move, produced⟩
            exact ⟨next, Or.inr (Or.inr (Or.inl ⟨request, typedRecognized⟩)), move, produced⟩
          · rintro ⟨next, _, move, produced⟩
            exact ⟨next, move, produced⟩
      | some request =>
        have same := HEContextEntry.Request.recognize_exact scopeRecognized
        subst task
        rw [encode_scope]
        constructor
        · intro compiled
          obtain ⟨next, result, output⟩ :=
            (scope_rules_exact environment policy code request world scope stack parents emitted after).mp compiled
          exact ⟨next, Or.inr (Or.inl ⟨request, scopeRecognized⟩),
            (HEContextEntry.step_iff request world scope stack parents emitted next).mpr result, output⟩
        · rintro ⟨next, _, step, output⟩
          exact (scope_rules_exact environment policy code request world scope stack parents emitted after).mpr
            ⟨next, (HEContextEntry.step_iff request world scope stack parents emitted next).mp step, output⟩
    | some request =>
      have sameTask := NativeRequest.recognize_exact recognized
      subst task
      simp only [encode_native]
      constructor
      · rintro ⟨r, listed, fires⟩
        rcases rule_cases listed with rfl | rfl | rfl | rfl | rfl | typed | queried | bodies | returns | application | primitive
        · obtain ⟨answers, updated, performed, result⟩ :=
            (HENativeOnTransform.native_rewrite_iff code environment.services
              request world scope stack parents emitted after).mp ((native_port code environment policy _ _).mp fires)
          refine ⟨⟨updated, scope, .returning answers, stack, parents, emitted⟩, Or.inl ⟨request, recognized⟩, ?_, result⟩
          exact (HEFocused.native_step_iff request world scope stack parents emitted _).mpr
            ⟨answers, updated, performed, rfl⟩
        · exact (by have bad := resume_tag fires; cases bad)
        · exact (by have bad := publish_tag fires; cases bad)
        · exact (by have bad := HEContextOnTransform.enters_only_tag fires; cases bad)
        · exact (by have bad := HEContextOnTransform.current_only_tag fires; cases bad)
        · exact (by have bad := typed_input_tag typed fires; cases bad)
        · exact (by have bad := invocation_input_tag queried fires; cases bad)
        · exact (by have bad := body_input_tag bodies fires; cases bad)
        · exact (by have bad := return_input_tag returns fires; cases bad)
        · exact (by have bad := application_input_tag application fires; cases bad)
        · rcases primitive_input_tag primitive fires with bad | bad <;> cases bad
      · rintro ⟨next, _, moved, result⟩
        obtain ⟨answers, updated, performed, rfl⟩ :=
          (HEFocused.native_step_iff request world scope stack parents emitted next).mp moved
        refine ⟨HENativeOnTransform.rule, by simp [rules], (native_port code environment policy _ _).mpr ?_⟩
        exact (HENativeOnTransform.native_rewrite_iff code environment.services
          request world scope stack parents emitted after).mpr ⟨answers, updated, performed, result⟩
  | returning answers =>
    simp only [encode_return]
    cases stack with
    | cons frame tail =>
      exact return_rules_exact environment policy code frame answers world scope tail parents emitted after
    | nil =>
      constructor
      · rintro ⟨r, listed, fires⟩
        rcases rule_cases listed with rfl | rfl | rfl | rfl | rfl | typed | queried | bodies | returns | application | primitive
        · exact (by have bad := HENativeOnTransform.input_tag fires; cases bad)
        · obtain ⟨parent, outer, _, rfl, result⟩ := (resume_rewrite_iff code _ _ _ _ _ _ _ _).mp fires
          exact ⟨⟨world, parent.scope, .returning answers, parent.stack, outer, emitted⟩, trivial, .resume, result⟩
        · obtain ⟨first, rest, _, rfl, rfl, result⟩ := (publish_rewrite_iff code _ _ _ _ _ _ _ _).mp fires
          exact ⟨⟨world, scope, .returning rest, [], [], emitted ++ [first]⟩, trivial, .publish, result⟩
        · exact (by have bad := HEContextOnTransform.enters_only_tag fires; cases bad)
        · exact (by have bad := HEContextOnTransform.current_only_tag fires; cases bad)
        · exact (by have bad := typed_input_tag typed fires; cases bad)
        · exact (by have bad := invocation_input_tag queried fires; cases bad)
        · exact (by have bad := body_input_tag bodies fires; cases bad)
        · obtain ⟨width, rfl⟩ := HEBodyReturnOnTransform.return_rule_origin returns
          exact (HEBodyReturnOnTransform.no_return_frame code _ width world scope answers parents emitted after fires).elim
        · exact (by have bad := application_input_tag application fires; cases bad)
        · rcases primitive_input_tag primitive fires with bad | bad <;> cases bad
      · rintro ⟨next, _, moved, result⟩
        have resumed := (HEFocused.return_step_iff world scope answers parents emitted next).mp moved
        cases parents with
        | cons parent outer =>
          simp only [HEFocused.returnNext, Option.some.injEq] at resumed
          subst next
          refine ⟨resumeRule, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
          exact (resume_rewrite_iff code _ _ _ _ _ _ _ _).mpr ⟨parent, outer, rfl, rfl, result⟩
        | nil =>
          cases answers with
          | nil => cases resumed
          | cons first rest =>
            simp only [HEFocused.returnNext, Option.some.injEq] at resumed
            subst next
            refine ⟨publishRule, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩
            exact (publish_rewrite_iff code _ _ _ _ _ _ _ _).mpr ⟨first, rest, rfl, rfl, rfl, result⟩

private abbrev program (code : Presentation Context World) (environment : WorldEnvironment Context World) (policy : Policy) :=
  specialized rows (relationGraph (operations code environment policy)) {r | r ∈ rules}

def theory (O : Type) [DecidableEq O] (code : Presentation Context World)
    (environment : WorldEnvironment Context World) (policy : Policy) : GSLT :=
  programSystem O (program code environment policy)

theorem ordinary_rule_shape {r : RuleWithCondition Nat Tm} (member : r ∈ rules) :
    r.rule.collect = [] ∧ r.rule.body.checks.all RuleSyntax.Presentation.Schematic.isGuard = true ∧
      r.RangeRestrictedWith := by
  rcases rule_cases member with rfl | rfl | rfl | rfl | rfl | typed | queried | bodies | returns | application | primitive
  · exact ⟨rfl, rfl, HENativeOnTransform.rule_restricted⟩
  · exact ⟨rfl, rfl, resume_restricted⟩
  · exact ⟨rfl, rfl, publish_restricted⟩
  · exact ⟨rfl, rfl, HEContextOnTransform.enter_restricted⟩
  · exact ⟨rfl, rfl, HEContextOnTransform.current_restricted⟩
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp typed
    exact ⟨rfl, rfl, HEAtomOnTransform.rule_restricted b⟩
  · obtain ⟨s, _, rfl⟩ := List.mem_map.mp queried
    exact ⟨rfl, rfl, HEInvocationOnTransform.rule_restricted s⟩
  · obtain ⟨width, rfl⟩ := HEBodyReturnOnTransform.body_rule_origin bodies
    exact ⟨rfl, rfl, PureContinuationRules.rule_restricted (.work 8) _ width⟩
  · obtain ⟨width, rfl⟩ := HEBodyReturnOnTransform.return_rule_origin returns
    exact ⟨rfl, rfl, PureContinuationRules.rule_restricted .consume _ width⟩
  · obtain ⟨width, rfl⟩ := application_rule_origin application
    exact ⟨rfl, rfl, PureContinuationRules.rule_restricted (.schedule 9) _ width⟩
  · obtain ⟨family, width, rfl⟩ := primitive_rule_origin primitive
    cases family with
    | plain => exact ⟨rfl, rfl, PureContinuationRules.rule_restricted (.schedule 3) _ width⟩
    | bindings => exact ⟨rfl, rfl, PureContinuationRules.world_rule_restricted (.work 10) _ width⟩

private theorem positive (code : Presentation Context World) (environment : WorldEnvironment Context World)
    (policy : Policy) : ∀ r ∈ program code environment policy, DeterminedPositive r :=
  relations_fragment (fun _ known => (ordinary_rule_shape known).1)
    (fun _ known => (ordinary_rule_shape known).2.1) (fun _ known => (ordinary_rule_shape known).2.2)

/-- Rewriting at a named live space, in the dialect's source terms. -/
def source : GSLT :=
  equalityGSLT (WorldConfiguration Context World) (fun before after =>
    Covered (HEFocused.focus before) ∧ WorldStepWith environment.arguments environment.view environment.services
      environment.dispatch environment.lookup policy before after)

theorem source_step_iff (before after : WorldConfiguration Context World) :
    (source environment policy).Step before after ↔
      WorldStepWith environment.arguments environment.view environment.services
        environment.dispatch environment.lookup policy before after :=
  ⟨And.right, fun step => ⟨all_covered _, step⟩⟩

theorem source_of_focus {before after : Focus Context World} (covered : Covered before)
    (step : HEFocused.Move environment.arguments environment.view environment.services
      environment.dispatch environment.lookup policy before after) :
    (source environment policy).Step (HEFocused.restore before) (HEFocused.restore after) := by
  exact ⟨by simpa only [HEFocused.focus_restore] using covered, HEFocused.restore_step step⟩

def Shows {O : Type} (code : Presentation Context World) (configuration : WorldConfiguration Context World)
    (state : SState O) : Prop :=
  ReadsBag state {encodeFocus code (HEFocused.focus configuration)}

theorem shows_unique {O : Type} [DecidableEq O] (code : Presentation Context World)
    {before after : WorldConfiguration Context World} {state : SState O}
    (left : Shows code before state) (right : Shows code after state) : before = after := by
  have readings := readsAs_unique (ReadsBag.readsAs left).1 (ReadsBag.readsAs left).2 (ReadsBag.readsAs right).2
  exact HEFocused.focusing.injective ((encodeFocus_injective code) (Multiset.singleton_inj.mp readings))

theorem realize_step {O : Type} [DecidableEq O] [Infinite O] (code : Presentation Context World)
    {before after : WorldConfiguration Context World} {first : SState O} (shown : Shows code before first)
    (step : (source environment policy).Step before after) :
    ∃ final, (theory O code environment policy).Step first final ∧ Shows code after final := by
  obtain ⟨covered, move⟩ := step
  obtain ⟨rule, listed, rewriting⟩ := (relation_step_iff environment policy code _ _).mpr
    ⟨HEFocused.focus after, covered, HEFocused.focus_step move, rfl⟩
  obtain ⟨compiled, member, matched⟩ :=
    (rewritesBy_relations_iff (P := {r | r ∈ rules})).mpr ⟨rule, listed, rewriting⟩
  obtain ⟨firing, admitted, _, result⟩ :=
    readsBag_forward_determined member (positive code environment policy compiled member) shown matched
  exact ⟨_, ⟨firing, admitted, rfl⟩, result⟩

theorem reflect_step {O : Type} [DecidableEq O] (code : Presentation Context World)
    {before : WorldConfiguration Context World} {first final : SState O} (shown : Shows code before first)
    (step : (theory O code environment policy).Step first final) :
    ∃ after, (source environment policy).Step before after ∧ Shows code after final := by
  obtain ⟨firing, admitted, rfl⟩ := step
  obtain ⟨bag, matched, result⟩ := readsBag_backward_determined shown firing admitted
    (makesDetermined_of_writes (positive code environment policy firing.rule firing.member).2.2)
  obtain ⟨next, covered, move, rfl⟩ := (relation_step_iff environment policy code _ bag).mp
    (rewritesBy_relations_iff.mp ⟨firing.rule, firing.member, matched⟩)
  refine ⟨HEFocused.restore next, ⟨covered, ?_⟩, ?_⟩
  · simpa only [HEFocused.restore_focus] using HEFocused.restore_step move
  · change ReadsBag _ {encodeFocus code (HEFocused.focus (HEFocused.restore next))}
    rw [HEFocused.focus_restore]
    exact result

theorem realize_path {O : Type} [DecidableEq O] [Infinite O] (code : Presentation Context World)
    {before after : WorldConfiguration Context World} {first : SState O} (shown : Shows code before first)
    (path : ExecutionPath (source environment policy) before after) :
    ∃ final, ∃ fired : ExecutionPath (theory O code environment policy) first final,
      Shows code after final ∧ fired.length = path.length := by
  induction path generalizing first with
  | refl => exact ⟨first, .refl first, shown, rfl⟩
  | cons step rest ih =>
    obtain ⟨_, fired, next⟩ := realize_step environment policy code shown step.down
    obtain ⟨final, remaining, last, length⟩ := ih next
    exact ⟨final, .cons ⟨fired⟩ remaining, last, congrArg (· + 1) length⟩

theorem reflect_path {O : Type} [DecidableEq O] (code : Presentation Context World)
    {before : WorldConfiguration Context World} {first final : SState O} (shown : Shows code before first)
    (fired : ExecutionPath (theory O code environment policy) first final) :
    ∃ after, ∃ path : ExecutionPath (source environment policy) before after,
      Shows code after final ∧ path.length = fired.length := by
  induction fired generalizing before with
  | refl => exact ⟨before, .refl before, shown, rfl⟩
  | cons step rest ih =>
    obtain ⟨_, moved, next⟩ := reflect_step environment policy code shown step.down
    obtain ⟨after, remaining, last, length⟩ := ih next
    exact ⟨after, .cons ⟨moved⟩ remaining, last, congrArg (· + 1) length⟩

theorem exact_length_iff {O : Type} [DecidableEq O] [Infinite O] (code : Presentation Context World)
    {before after : WorldConfiguration Context World} {first : SState O} (shown : Shows code before first) (n : Nat) :
    (∃ path : ExecutionPath (source environment policy) before after, path.length = n) ↔
      ∃ final, ∃ fired : ExecutionPath (theory O code environment policy) first final,
        Shows code after final ∧ fired.length = n := by
  constructor
  · rintro ⟨path, length⟩
    obtain ⟨final, fired, last, same⟩ := realize_path environment policy code shown path
    exact ⟨final, fired, last, same.trans length⟩
  · rintro ⟨final, fired, last, length⟩
    obtain ⟨reached, path, readBack, same⟩ := reflect_path environment policy code shown fired
    have eq := shows_unique code readBack last
    subst reached
    exact ⟨path, same.trans length⟩

private theorem path_endpoint {system : GSLT} {first last final : ExecutionObject system}
    (path : ExecutionPath system first last) (same : last = final) :
    ∃ moved : ExecutionPath system first final, moved.length = path.length := by
  cases same
  exact ⟨path, rfl⟩

/-- Publishing a complete root batch takes exactly one source event per
occurrence, regardless of the length or contents of the prior history. -/
theorem publish_path (world : World) (scope : Context) (answers emitted : List Result) :
    ∃ path : ExecutionPath (source environment policy)
      (HEFocused.restore ⟨world, scope, .returning answers, [], [], emitted⟩)
      (HEFocused.restore ⟨world, scope, .returning [], [], [], emitted ++ answers⟩),
      path.length = answers.length := by
  induction answers generalizing emitted with
  | nil =>
    let terminal := fun seen : List Result => HEFocused.restore ⟨world, scope, .returning [], [], [], seen⟩
    have same := congrArg terminal (List.append_nil emitted).symm
    exact path_endpoint (system := source environment policy) (.refl (terminal emitted)) same
  | cons first rest ih =>
    obtain ⟨tail, exactLength⟩ := ih (emitted ++ [first])
    let terminal := fun seen : List Result => HEFocused.restore ⟨world, scope, .returning [], [], [], seen⟩
    have same := congrArg terminal (List.append_assoc emitted [first] rest)
    obtain ⟨aligned, sameLength⟩ := path_endpoint tail same
    exact ⟨.cons ⟨source_of_focus environment policy trivial .publish⟩ aligned,
      congrArg (· + 1) (sameLength.trans exactLength)⟩

/-- Parent identities are stored nearest first; the last one is the
root. If there is no saved parent, the active identity is the root. -/
def rootScope (scope : Context) (parents : List (Parent Context)) : Context :=
  parents.foldl (fun _ saved => saved.scope) scope

/-- Returning past empty parent continuations spends one transition per
context and one per published occurrence. The size of the already
published history is not in this count. -/
theorem return_and_publish_path (world : World) (scope : Context) (answers emitted : List Result)
    (parents : List (Parent Context)) (empty : ∀ saved ∈ parents, saved.stack = []) :
    ∃ path : ExecutionPath (source environment policy)
      (HEFocused.restore ⟨world, scope, .returning answers, [], parents, emitted⟩)
      (HEFocused.restore ⟨world, rootScope scope parents, .returning [], [], [], emitted ++ answers⟩),
      path.length = answers.length + parents.length := by
  induction parents generalizing scope with
  | nil => exact publish_path environment policy world scope answers emitted
  | cons saved older ih =>
    have stackEmpty := empty saved List.mem_cons_self
    obtain ⟨tail, length⟩ := ih saved.scope (fun parent member => empty parent (List.mem_cons_of_mem _ member))
    have transfer := source_of_focus environment policy
      (before := ⟨world, scope, .returning answers, [], saved :: older, emitted⟩) trivial
      (HEFocused.Move.resume (parent := saved))
    rw [stackEmpty] at transfer
    exact ⟨.cons ⟨transfer⟩ tail, congrArg (· + 1) length⟩

theorem finished_has_no_firing {O : Type} [DecidableEq O] (code : Presentation Context World)
    (world : World) (scope : Context) (emitted : List Result) {start final : SState O}
    (shown : Shows code (HEFocused.restore ⟨world, scope, .returning [], [], [], emitted⟩) start) :
    ¬ (theory O code environment policy).Step start final := by
  intro fired
  obtain ⟨after, ⟨_, moved⟩, _⟩ := reflect_step environment policy code shown fired
  have reported := HEFocused.focus_step moved
  rw [HEFocused.focus_restore] at reported
  have impossible := (HEFocused.return_step_iff world scope [] [] emitted _).mp reported
  cases impossible

end Execution

end Mettapedia.Languages.MeTTa.SpaceTheory.HEControlOnTransform
