import Mettapedia.Languages.MeTTa.SpaceTheory.HEBodyEntry
import Mettapedia.Languages.MeTTa.SpaceTheory.HEReturnEntry
import Mettapedia.Languages.MeTTa.SpaceTheory.HESnapshotEntry
import Mettapedia.Languages.MeTTa.SpaceTheory.HEWorkView
import Mettapedia.GSLT.Compilation.Uniform.PureContinuationRules

/-! The two read-only HE boundaries share the same continuation splice.
Body scheduling consults its actual scope; returning supplies only the
top continuation and the batch. Neither port can replace the world. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEBodyReturnOnTransform

open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result WorldEnvironment WorldServices)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Task Continuation)
open Mettapedia.Languages.MeTTa.HE.ContextualData (taskData taskData_injective continuationData continuationData_injective)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic (Tm)
open RuleSyntax.ComputedConditions (Relations RelationStep RuleWithCondition)
open Mettapedia.GSLT.Compilation.Uniform
open PureContinuationRules (Width Ambient)
open StateRulesOnTheStep (fields fields_injective packet)
open HEFocused (Leaf Parent)
open HEWorkView (leafView)
open HENativeOnTransform
  (Presentation atom atom_injective workFields commonFields stackField parentsField historyField answerField returnAtom)

variable {Context World : Type}

def bodyPort : Width → Nat
  | .direct => 12
  | .one => 13
  | .two => 16

def returnPort : Width → Nat
  | .direct => 14
  | .one => 15
  | .two => 17

def bodyRule (width : Width) : RuleWithCondition Nat Tm :=
  PureContinuationRules.rule (.work 8) (bodyPort width) width

def returnRule (width : Width) : RuleWithCondition Nat Tm :=
  PureContinuationRules.rule .consume (returnPort width) width

def bodyRules : List (RuleWithCondition Nat Tm) := [bodyRule .direct, bodyRule .one]

def returnRules : List (RuleWithCondition Nat Tm) := [returnRule .direct, returnRule .one]

theorem body_rule_mem (width : Width) (bound : width.slots.length ≤ 1) : bodyRule width ∈ bodyRules := by
  cases width <;> simp_all [bodyRules, Width.slots]

theorem return_rule_mem (width : Width) (bound : width.slots.length ≤ 1) : returnRule width ∈ returnRules := by
  cases width <;> simp_all [returnRules, Width.slots]

theorem body_rule_origin {r : RuleWithCondition Nat Tm} (member : r ∈ bodyRules) :
    ∃ w, r = bodyRule w := by
  simp only [bodyRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same
  · exact ⟨.direct, same⟩
  · exact ⟨.one, same⟩

theorem return_rule_origin {r : RuleWithCondition Nat Tm} (member : r ∈ returnRules) :
    ∃ w, r = returnRule w := by
  simp only [returnRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same
  · exact ⟨.direct, same⟩
  · exact ⟨.one, same⟩

theorem body_input_tag {rel : Relations} {width : Width} {tag : Nat} {items : List Expr} {after : Multiset Expr}
    (step : RelationStep rel (bodyRule width) {packet tag items} after) : 8 = tag :=
  PureContinuationRules.input_tag step

theorem return_input_tag {rel : Relations} {width : Width} {tag : Nat} {items : List Expr} {after : Multiset Expr}
    (step : RelationStep rel (returnRule width) {packet tag items} after) : 2 = tag :=
  PureContinuationRules.input_tag step

theorem no_return_frame (code : Presentation Context World) (rel : Relations) (width : Width)
    (w : World) (scope : Context) (answers : List Result) (parents : List (Parent Context))
    (emitted : List Result) (after : Multiset Expr) :
    ¬ RelationStep rel (returnRule width) {returnAtom code w scope answers [] parents emitted} after :=
  PureContinuationRules.no_consume_empty rel (returnPort width) width (atom (code.world w))
    (atom (code.context scope)) (parentsField code parents) (historyField emitted) (answerField answers) after

def frameData (frames : List Continuation) : List Expr := frames.map (atom ∘ continuationData)

def replyData (body : Leaf) (frames : List Continuation) : Expr :=
  fields (.sym (leafView body).1 :: fields (leafView body).2 :: frameData frames)

def bodyRead (code : Presentation Context World) (env : WorldEnvironment Context World) (p : Policy)
    (width : Width) (asked : List Expr) (reply : Expr) : Prop :=
  ∃ (w : World) (scope : Context) (task : Task) (body : Leaf) (frames : List Continuation),
    asked = [atom (code.world w), atom (code.context scope), atom (taskData task)] ∧
      HEBodyEntry.Plan (env.view w scope) env.lookup p task body frames ∧
      frames.length = width.slots.length ∧ reply = replyData body frames

def returnRead (services : WorldServices Context World) (p : Policy) (width : Width)
    (asked : List Expr) (reply : Expr) : Prop :=
  ∃ (frame : Continuation) (answers : List Result) (body : Leaf) (frames : List Continuation),
    asked = [atom (continuationData frame), answerField answers] ∧
      HESnapshotEntry.ReturnPlan services p frame answers body frames ∧
      frames.length = width.slots.length ∧ reply = replyData body frames

def operations (code : Presentation Context World) (env : WorldEnvironment Context World) (p : Policy) : Relations
  | 12, asked, reply => bodyRead code env p .direct asked reply
  | 13, asked, reply => bodyRead code env p .one asked reply
  | 14, asked, reply => returnRead env.services p .direct asked reply
  | 15, asked, reply => returnRead env.services p .one asked reply
  | 16, asked, reply => bodyRead code env p .two asked reply
  | 17, asked, reply => returnRead env.services p .two asked reply
  | _, _, _ => False

def ambient (code : Presentation Context World) (w : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) (payload : Expr) : Ambient :=
  ⟨atom (code.world w), atom (code.context scope), stackField stack, parentsField code parents,
    historyField emitted, payload⟩

def requestAtom (code : Presentation Context World) (task : Task) (w : World) (scope : Context)
    (stack : List Continuation) (parents : List (Parent Context)) (emitted : List Result) : Expr :=
  packet 8 (workFields code task w scope stack parents emitted)

def outcomeAtom (code : Presentation Context World) (w : World) (scope : Context) (body : Leaf)
    (front stack : List Continuation) (parents : List (Parent Context)) (emitted : List Result) : Expr :=
  packet (leafView body).1 (commonFields code w scope (front ++ stack) parents emitted ++ (leafView body).2)

theorem outcome_exact (code : Presentation Context World) (w : World) (scope : Context) (body : Leaf)
    (front stack : List Continuation) (parents : List (Parent Context)) (emitted : List Result) (payload : Expr) :
    PureContinuationRules.outcome (ambient code w scope stack parents emitted payload) (.sym (leafView body).1)
      (fields (leafView body).2) (frameData front) = outcomeAtom code w scope body front stack parents emitted := by
  rw [outcomeAtom, packet, StateRulesOnTheStep.fields_append]
  simp only [PureContinuationRules.outcome, ambient, commonFields, List.foldr_cons, List.foldr_nil,
    stackField, StateRulesOnTheStep.spine, List.map_append, StateRulesOnTheStep.fields_append, frameData]

private theorem body_operation_exact (code : Presentation Context World) (env : WorldEnvironment Context World)
    (p : Policy) (width : Width) (w : World) (scope : Context) (task : Task) (data : Expr) :
    operations code env p (bodyPort width) [atom (code.world w), atom (code.context scope), atom (taskData task)] data ↔
      ∃ body frames, HEBodyEntry.Plan (env.view w scope) env.lookup p task body frames ∧
        frames.length = width.slots.length ∧ data = replyData body frames := by
  have read : operations code env p (bodyPort width) = bodyRead code env p width := by cases width <;> rfl
  rw [read, bodyRead]
  constructor
  · rintro ⟨world, ctx, source, body, frames, taken, prepared, count, result⟩
    simp only [List.cons.injEq, and_true, atom_injective.eq_iff, code.world_injective.eq_iff,
      code.context_injective.eq_iff, taskData_injective.eq_iff] at taken
    obtain ⟨rfl, rfl, rfl⟩ := taken
    exact ⟨body, frames, prepared, count, result⟩
  · rintro ⟨body, frames, prepared, count, result⟩
    exact ⟨w, scope, task, body, frames, rfl, prepared, count, result⟩

private theorem return_operation_exact (code : Presentation Context World) (env : WorldEnvironment Context World)
    (p : Policy) (width : Width) (frame : Continuation) (answers : List Result) (data : Expr) :
    operations code env p (returnPort width) [atom (continuationData frame), answerField answers] data ↔
      ∃ body frames, HESnapshotEntry.ReturnPlan env.services p frame answers body frames ∧
        frames.length = width.slots.length ∧ data = replyData body frames := by
  have read : operations code env p (returnPort width) = returnRead env.services p width := by cases width <;> rfl
  rw [read, returnRead]
  constructor
  · rintro ⟨actual, received, body, frames, taken, prepared, count, result⟩
    simp only [List.cons.injEq, and_true, atom_injective.eq_iff, continuationData_injective.eq_iff,
      HENativeOnTransform.answerField_injective.eq_iff] at taken
    obtain ⟨rfl, rfl⟩ := taken
    exact ⟨body, frames, prepared, count, result⟩
  · rintro ⟨body, frames, prepared, count, result⟩
    exact ⟨frame, answers, body, frames, rfl, prepared, count, result⟩

theorem body_exact (code : Presentation Context World) (env : WorldEnvironment Context World) (p : Policy)
    (width : Width) (task : Task) (w : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) (after : Multiset Expr) :
    RelationStep (operations code env p) (bodyRule width)
        {requestAtom code task w scope stack parents emitted} after ↔
      ∃ body frames, HEBodyEntry.Plan (env.view w scope) env.lookup p task body frames ∧
        frames.length = width.slots.length ∧
        after = {outcomeAtom code w scope body frames stack parents emitted} := by
  let a := ambient code w scope stack parents emitted (atom (taskData task))
  have parsed := PureContinuationRules.step_exact (operations code env p) (.work 8) (bodyPort width) width a after
  simp only [PureContinuationRules.Input.mode] at parsed
  rw [show requestAtom code task w scope stack parents emitted =
      PureContinuationRules.Input.message (.work 8) a from rfl, bodyRule, parsed]
  constructor
  · rintro ⟨tag, tail, first, _, licensed, result⟩
    obtain ⟨body, frames, prepared, count, data⟩ := (body_operation_exact code env p width w scope task _).mp licensed
    have same := fields_injective data
    simp only [List.cons.injEq] at same
    obtain ⟨rfl, rfl, rfl⟩ := same
    exact ⟨body, frames, prepared, count, result.trans (congrArg (fun term => ({term} : Multiset Expr))
      (outcome_exact code w scope body frames stack parents emitted _))⟩
  · rintro ⟨body, frames, prepared, count, result⟩
    exact ⟨.sym (leafView body).1, fields (leafView body).2, frameData frames,
      (List.length_map _).trans count,
      (body_operation_exact code env p width w scope task _).mpr ⟨body, frames, prepared, count, rfl⟩,
      result.trans (congrArg (fun term => ({term} : Multiset Expr))
        (outcome_exact code w scope body frames stack parents emitted _).symm)⟩

theorem return_exact (code : Presentation Context World) (env : WorldEnvironment Context World) (p : Policy)
    (width : Width) (frame : Continuation) (answers : List Result) (w : World) (scope : Context)
    (stack : List Continuation) (parents : List (Parent Context)) (emitted : List Result) (after : Multiset Expr) :
    RelationStep (operations code env p) (returnRule width) {returnAtom code w scope answers (frame :: stack) parents emitted} after ↔
      ∃ body frames, HESnapshotEntry.ReturnPlan env.services p frame answers body frames ∧
        frames.length = width.slots.length ∧
        after = {outcomeAtom code w scope body frames stack parents emitted} := by
  let a := ambient code w scope stack parents emitted (answerField answers)
  have parsed := PureContinuationRules.step_exact (operations code env p) (.returned (atom (continuationData frame)))
    (returnPort width) width a after
  simp only [PureContinuationRules.Input.mode] at parsed
  rw [show returnAtom code w scope answers (frame :: stack) parents emitted =
      PureContinuationRules.Input.message (.returned (atom (continuationData frame))) a from rfl, returnRule, parsed]
  constructor
  · rintro ⟨tag, tail, first, _, licensed, result⟩
    obtain ⟨body, frames, prepared, count, data⟩ := (return_operation_exact code env p width frame answers _).mp licensed
    have same := fields_injective data
    simp only [List.cons.injEq] at same
    obtain ⟨rfl, rfl, rfl⟩ := same
    exact ⟨body, frames, prepared, count, result.trans (congrArg (fun term => ({term} : Multiset Expr))
      (outcome_exact code w scope body frames stack parents emitted _))⟩
  · rintro ⟨body, frames, prepared, count, result⟩
    exact ⟨.sym (leafView body).1, fields (leafView body).2, frameData frames,
      (List.length_map _).trans count,
      (return_operation_exact code env p width frame answers _).mpr ⟨body, frames, prepared, count, rfl⟩,
      result.trans (congrArg (fun term => ({term} : Multiset Expr))
        (outcome_exact code w scope body frames stack parents emitted _).symm)⟩

/-! The same state form admits scheduling that needs only the pending
task, without passing either the space or any enclosing continuation. -/

def scheduleRead (plan : Task → Leaf → List Continuation → Prop) (width : Width)
    (asked : List Expr) (reply : Expr) : Prop :=
  ∃ task body frames, asked = [atom (taskData task)] ∧ plan task body frames ∧
    frames.length = width.slots.length ∧ reply = replyData body frames

theorem schedule_read_exact (plan : Task → Leaf → List Continuation → Prop) (width : Width)
    (task : Task) (data : Expr) :
    scheduleRead plan width [atom (taskData task)] data ↔
      ∃ body frames, plan task body frames ∧ frames.length = width.slots.length ∧ data = replyData body frames := by
  constructor
  · rintro ⟨source, body, frames, asked, planned, count, built⟩
    have same := taskData_injective (atom_injective (List.cons.inj asked).1)
    subst source
    exact ⟨body, frames, planned, count, built⟩
  · rintro ⟨body, frames, planned, count, built⟩
    exact ⟨task, body, frames, rfl, planned, count, built⟩

theorem schedule_exact (code : Presentation Context World) (plan : Task → Leaf → List Continuation → Prop)
    (tag port : Nat) (width : Width) (rel : Relations)
    (operation : ∀ args reply, rel port args reply ↔ scheduleRead plan width args reply)
    (task : Task) (w : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) (after : Multiset Expr) :
    RelationStep rel (PureContinuationRules.rule (.schedule tag) port width)
      {packet tag (workFields code task w scope stack parents emitted)} after ↔
      ∃ body frames, plan task body frames ∧ frames.length = width.slots.length ∧
        after = {outcomeAtom code w scope body frames stack parents emitted} := by
  let a := ambient code w scope stack parents emitted (atom (taskData task))
  have schematic := PureContinuationRules.step_exact rel (.schedule tag) port width a after
  simp only [PureContinuationRules.Input.mode, PureContinuationRules.Input.arguments] at schematic
  rw [show packet tag (workFields code task w scope stack parents emitted) =
    PureContinuationRules.Input.message (.schedule tag) a from rfl, schematic]
  constructor
  · rintro ⟨chosen, tail, front, _, licensed, result⟩
    obtain ⟨body, frames, planned, count, same⟩ := (schedule_read_exact plan width task _).mp
      ((operation _ _).mp licensed)
    have matching := fields_injective same
    simp only [List.cons.injEq] at matching
    obtain ⟨rfl, rfl, rfl⟩ := matching
    exact ⟨body, frames, planned, count, result.trans (congrArg (fun term => ({term} : Multiset Expr))
      (outcome_exact code w scope body frames stack parents emitted _))⟩
  · rintro ⟨body, frames, planned, count, result⟩
    exact ⟨.sym (leafView body).1, fields (leafView body).2, frameData frames, (List.length_map _).trans count,
      (operation _ _).mpr ((schedule_read_exact plan width task _).mpr ⟨body, frames, planned, count, rfl⟩),
      result.trans (congrArg (fun term => ({term} : Multiset Expr))
        (outcome_exact code w scope body frames stack parents emitted _).symm)⟩

def worldRead (code : Presentation Context World)
    (plan : World → Context → Task → World → Leaf → List Continuation → Prop)
    (width : Width) (asked : List Expr) (reply : Expr) : Prop :=
  ∃ world scope task next body frames,
    asked = [atom (code.world world), atom (code.context scope), atom (taskData task)] ∧
    plan world scope task next body frames ∧ frames.length = width.slots.length ∧
    reply = .app (atom (code.world next)) (replyData body frames)

private theorem world_read_exact (code : Presentation Context World)
    (plan : World → Context → Task → World → Leaf → List Continuation → Prop)
    (width : Width) (world : World) (scope : Context) (task : Task) (data : Expr) :
    worldRead code plan width [atom (code.world world), atom (code.context scope), atom (taskData task)] data ↔
      ∃ next body frames, plan world scope task next body frames ∧ frames.length = width.slots.length ∧
        data = .app (atom (code.world next)) (replyData body frames) := by
  constructor
  · rintro ⟨w, c, actual, next, body, frames, given, licensed, count, built⟩
    simp only [List.cons.injEq, and_true, atom_injective.eq_iff, code.world_injective.eq_iff,
      code.context_injective.eq_iff, taskData_injective.eq_iff] at given
    obtain ⟨rfl, rfl, rfl⟩ := given
    exact ⟨next, body, frames, licensed, count, built⟩
  · rintro ⟨next, body, frames, licensed, count, built⟩
    exact ⟨world, scope, task, next, body, frames, rfl, licensed, count, built⟩

theorem world_schedule_exact (code : Presentation Context World)
    (plan : World → Context → Task → World → Leaf → List Continuation → Prop)
    (tag port : Nat) (width : Width) (rel : Relations)
    (operation : ∀ args reply, rel port args reply ↔ worldRead code plan width args reply)
    (task : Task) (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) (after : Multiset Expr) :
    RelationStep rel (PureContinuationRules.worldRule (.work tag) port width)
      {packet tag (workFields code task world scope stack parents emitted)} after ↔
      ∃ next body frames, plan world scope task next body frames ∧ frames.length = width.slots.length ∧
        after = {outcomeAtom code next scope body frames stack parents emitted} := by
  let a := ambient code world scope stack parents emitted (atom (taskData task))
  have schematic := PureContinuationRules.world_step_exact rel (.work tag) port width a after
  simp only [PureContinuationRules.Input.mode, PureContinuationRules.Input.arguments] at schematic
  rw [show packet tag (workFields code task world scope stack parents emitted) =
    PureContinuationRules.Input.message (.work tag) a from rfl, schematic]
  constructor
  · rintro ⟨updated, chosen, tail, front, _, read, result⟩
    obtain ⟨next, body, frames, licensed, count, same⟩ := (world_read_exact code plan width world scope task _).mp
      ((operation _ _).mp read)
    have received := Expr.app.inj same
    have fieldsEq := fields_injective received.2
    simp only [List.cons.injEq] at fieldsEq
    obtain ⟨rfl, rfl, rfl⟩ := fieldsEq
    have out := outcome_exact code next scope body frames stack parents emitted (atom (taskData task))
    rw [received.1] at result
    exact ⟨next, body, frames, licensed, count, result.trans (congrArg (fun term => ({term} : Multiset Expr)) out)⟩
  · rintro ⟨next, body, frames, licensed, count, result⟩
    exact ⟨atom (code.world next), .sym (leafView body).1, fields (leafView body).2, frameData frames,
      (List.length_map _).trans count,
      (operation _ _).mpr ((world_read_exact code plan width world scope task _).mpr ⟨next, body, frames, licensed, count, rfl⟩),
      result.trans (congrArg (fun term => ({term} : Multiset Expr))
        (outcome_exact code next scope body frames stack parents emitted (atom (taskData task))).symm)⟩

end Mettapedia.Languages.MeTTa.SpaceTheory.HEBodyReturnOnTransform
