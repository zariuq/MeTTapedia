import Mettapedia.Languages.MeTTa.SpaceTheory.HEInvocationEntry
import Mettapedia.Languages.MeTTa.SpaceTheory.HEWorkView

/-!
# HE invocation and retained work on the Transform step

There are three schemas, indexed by the number of new continuation
frames. The primitive condition distinguishes the complete current
equation query, a captured work item, and the grounded host operation.
It does not receive the enclosing stack or publication history. The
rules append the new frames to that same underlying continuation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEInvocationOnTransform

open Mettapedia.Languages.MeTTa.HE.Spec.Eval (GroundedDispatch)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result WorldEnvironment)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Continuation)
open Mettapedia.Languages.MeTTa.HE.ContextualData (taskData taskData_injective continuationData)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic (Tm inst)
open RuleSyntax.ComputedConditions (Relations RelationStep Condition RuleWithCondition)
open HEFocused (Leaf Parent)
open HEInvocationEntry (Request Reply Licensed continuation)
open HEWorkView (leafView)
open HENativeOnTransform
  (Presentation atom atom_injective commonFields workFields stackField parentsField historyField)
open Mettapedia.GSLT.Compilation.RootRewritesOnTheStep (appTerm symTerm inst_appTerm)
open Mettapedia.GSLT.Compilation.Uniform
open StateRulesOnTheStep (fields fields_injective packet pattern packet_eq_iff instantiate_fields
  instantiate_packet instance_var)

variable {Context World : Type}

inductive Shape where
  | direct | one | two

def shapes : List Shape := [.direct, .one, .two]

theorem shape_mem (shape : Shape) : shape ∈ shapes := by cases shape <;> simp [shapes]

def Shape.port : Shape → Nat
  | .direct => 9
  | .one => 10
  | .two => 11

def Shape.slots : Shape → List Nat
  | .direct => []
  | .one => [9]
  | .two => [9, 10]

theorem port_injective : Function.Injective Shape.port := by
  intro a b same
  cases a <;> cases b <;> simp_all [Shape.port]

theorem shape_of_length {frames : List Continuation} (bounded : frames.length ≤ 2) :
    ∃ s : Shape, frames.length = s.slots.length := by
  cases frames with
  | nil => exact ⟨.direct, rfl⟩
  | cons first tail =>
    cases tail with
    | nil => exact ⟨.one, rfl⟩
    | cons second rest =>
      cases rest with
      | nil => exact ⟨.two, rfl⟩
      | cons third more => simp at bounded

def requestAtom (code : Presentation Context World) (request : Request) (w : World) (c : Context)
    (stack : List Continuation) (parents : List (Parent Context)) (emitted : List Result) : Expr :=
  packet 7 (workFields code request.task w c stack parents emitted)

def encodedFrames (frames : List Continuation) : List Expr := frames.map (atom ∘ continuationData)

def replyFields (code : Presentation Context World) (w' : World) (work : Leaf) (frames : List Continuation) : List Expr :=
  .sym (leafView work).1 :: atom (code.world w') :: fields (leafView work).2 :: encodedFrames frames

def outcomeAtom (code : Presentation Context World) (w' : World) (c : Context) (work : Leaf)
    (frames stack : List Continuation) (parents : List (Parent Context)) (emitted : List Result) : Expr :=
  packet (leafView work).1 (commonFields code w' c (frames ++ stack) parents emitted ++ (leafView work).2)

abbrev ReplyAuthority (Context World : Type) := World → Context → Request → Reply → World → Prop

def operationsFrom (code : Presentation Context World) (dispatch : GroundedDispatch) (p : Policy)
    (authorize : ReplyAuthority Context World) : Relations :=
  fun name input result =>
    ∃ (s : Shape) (r : Request) (w : World) (scope : Context) (reply : Reply) (next : World)
      (body : Leaf) (frames : List Continuation),
      name = Shape.port s ∧ input = [atom (code.world w), atom (code.context scope), atom (taskData r.task)] ∧
      authorize w scope r reply next ∧ continuation p dispatch r reply = some (body, frames) ∧
      frames.length = s.slots.length ∧ result = fields (replyFields code next body frames)

def operations (code : Presentation Context World) (env : WorldEnvironment Context World) (p : Policy) : Relations :=
  operationsFrom code env.dispatch p (Licensed env p)

theorem operation_exact (code : Presentation Context World) (env : WorldEnvironment Context World)
    (p : Policy) (s : Shape) (r : Request) (w : World) (c : Context) (result : Expr) :
    operations code env p s.port [atom (code.world w), atom (code.context c), atom (taskData r.task)] result ↔
      ∃ reply next body frames, Licensed env p w c r reply next ∧
        continuation p env.dispatch r reply = some (body, frames) ∧ frames.length = s.slots.length ∧
        result = fields (replyFields code next body frames) := by
  constructor
  · rintro ⟨other, request, before, context, reply, next, body, frames, port, inputs, allowed, planned, width, answer⟩
    obtain rfl : s = other := port_injective port
    simp only [List.cons.injEq, and_true, atom_injective.eq_iff,
      code.world_injective.eq_iff, code.context_injective.eq_iff,
      taskData_injective.eq_iff, Request.task_injective.eq_iff] at inputs
    obtain ⟨rfl, rfl, rfl⟩ := inputs
    exact ⟨reply, next, body, frames, allowed, planned, width, answer⟩
  · rintro ⟨reply, next, body, frames, allowed, planned, width, answer⟩
    exact ⟨s, r, w, c, reply, next, body, frames, rfl, rfl, allowed, planned, width, answer⟩

private def varList (keys : List Nat) : List Tm := keys.map .var
private def taken : Tm := pattern 7 (varList [0, 1, 2, 3, 4, 5])

private def made (s : Shape) : Tm :=
  appTerm (.var 6)
    (([.var 7, .var 1, (varList s.slots).foldr appTerm (.var 2), .var 3, .var 4] : List Tm).foldr appTerm (.var 8))

private def ask (s : Shape) : Condition Nat Tm :=
  { name := s.port, arguments := varList [0, 1, 5],
    value := (varList (6 :: 7 :: 8 :: s.slots)).foldr appTerm (symTerm 0) }

def rule (s : Shape) : RuleWithCondition Nat Tm := StateRulesOnTheStep.rule taken (made s) [ask s]

def rules : List (RuleWithCondition Nat Tm) := shapes.map rule

theorem asks_port (s : Shape) (c : Condition Nat Tm) (member : c ∈ (rule s).conditions) : c.name = s.port := by
  obtain rfl : c = ask s := List.mem_singleton.mp member
  rfl

theorem input_tag {rel : Relations} {s : Shape} {tag : Nat} {items : List Expr} {after : Multiset Expr}
    (step : RelationStep rel (rule s) {packet tag items} after) : 7 = tag :=
  StateRulesOnTheStep.input_tag step

theorem rule_restricted (s : Shape) : (rule s).RangeRestrictedWith := by
  apply StateRulesOnTheStep.restricted
  intro x member
  let ends := RuleSyntax.Machines.unknowns (made s)
  let bound := RuleSyntax.Machines.unknowns taken ++ RuleSyntax.Machines.unknowns (ask s).value
  have included : ends.all bound.contains = true := by cases s <;> decide +kernel
  have present : x ∈ bound := List.contains_iff_mem.mp ((List.all_eq_true.mp included) x member)
  rcases List.mem_append.mp present with available | produced
  · exact Or.inl available
  · exact Or.inr ⟨ask s, List.mem_cons_self, produced⟩

private theorem instantiate_vars (v : Nat → Expr) (keys : List Nat) :
    (varList keys).map (inst v) = keys.map v := by
  induction keys with
  | nil => rfl
  | cons first rest ih =>
    simp only [varList, List.map_cons, instance_var] at ih ⊢
    rw [ih]

private theorem instantiate_open (v : Nat → Expr) (keys : List Nat) (tail : Nat) :
    inst v ((varList keys).foldr appTerm (.var tail)) = (keys.map v).foldr Expr.app (v tail) := by
  induction keys with
  | nil => rfl
  | cons first rest ih =>
    simp only [varList, List.map_cons, List.foldr_cons, inst_appTerm, instance_var] at ih ⊢
    rw [ih]

private theorem stack_append (new old : List Continuation) :
    stackField (new ++ old) = (encodedFrames new).foldr Expr.app (stackField old) := by
  simp only [stackField, StateRulesOnTheStep.spine, List.map_append, StateRulesOnTheStep.fields_append, encodedFrames]

private theorem field_cons (first : Expr) (rest : List Expr) :
    fields (first :: rest) = .app first (fields rest) := rfl

theorem rule_exact (code : Presentation Context World) (env : WorldEnvironment Context World) (p : Policy)
    (s : Shape) (r : Request) (w : World) (c : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) (after : Multiset Expr) :
    RelationStep (operations code env p) (rule s) {requestAtom code r w c stack parents emitted} after ↔
      ∃ reply next body frames, Licensed env p w c r reply next ∧
        continuation p env.dispatch r reply = some (body, frames) ∧ frames.length = s.slots.length ∧
        after = {outcomeAtom code next c body frames stack parents emitted} := by
  rw [rule, StateRulesOnTheStep.instance_iff]
  constructor
  · rintro ⟨v, matched, reads, output⟩
    simp only [taken, instantiate_packet, instantiate_vars, requestAtom, workFields, commonFields,
      List.cons_append, List.nil_append, List.map_cons, List.map_nil, packet_eq_iff, true_and, List.cons.injEq,
      and_true] at matched
    obtain ⟨world, scope, k, parents', history, task⟩ := matched
    have computed := reads (ask s) List.mem_cons_self
    simp only [ask, instantiate_fields, instantiate_vars, List.map_cons, List.map_nil, world, scope, task] at computed
    obtain ⟨reply, next, body, frames, allowed, planned, width, fields'⟩ :=
      (operation_exact code env p s r w c _).mp computed
    have same := fields_injective fields'
    simp only [replyFields, List.cons.injEq] at same
    obtain ⟨tag, world', leaf, entered⟩ := same
    refine ⟨reply, next, body, frames, allowed, planned, width, ?_⟩
    simpa only [made, inst_appTerm, instance_var, List.foldr_cons, List.foldr_nil, instantiate_open,
      outcomeAtom, packet, commonFields, List.cons_append, List.nil_append, field_cons,
      stack_append, tag, world', leaf, entered, scope, k, parents', history]
      using output
  · rintro ⟨reply, next, body, frames, allowed, planned, width, rfl⟩
    let slots := workFields code r.task w c stack parents emitted ++ replyFields code next body frames
    let v := fun name : Nat => slots[name]?.getD (.sym 0)
    have accept := (operation_exact code env p s r w c (fields (replyFields code next body frames))).mpr
      ⟨reply, next, body, frames, allowed, planned, width, rfl⟩
    have maps : s.slots.map v = encodedFrames frames := by
      cases s with
      | direct =>
        obtain rfl := List.length_eq_zero_iff.mp (show frames.length = 0 from width)
        rfl
      | one =>
        cases frames with
        | nil => cases width
        | cons head rest =>
          obtain rfl := List.length_eq_zero_iff.mp (Nat.succ.inj width)
          rfl
      | two =>
        cases frames with
        | nil => cases width
        | cons first rest =>
          cases rest with
          | nil => cases width
          | cons second tail =>
            obtain rfl := List.length_eq_zero_iff.mp (Nat.succ.inj (Nat.succ.inj width))
            rfl
    refine ⟨v, ?_, ?_, ?_⟩
    · simp [taken, instantiate_packet, instantiate_vars, requestAtom, workFields, commonFields, v, slots]
    · intro condition member
      obtain rfl : condition = ask s := List.mem_singleton.mp member
      simp only [ask, instantiate_fields, instantiate_vars, List.map_cons, List.map_nil, maps]
      exact accept
    · simp only [made, inst_appTerm, instance_var, List.foldr_cons, List.foldr_nil,
        instantiate_open, maps, outcomeAtom, packet, commonFields, List.cons_append, List.nil_append,
        field_cons, stack_append]
      rfl

end Mettapedia.Languages.MeTTa.SpaceTheory.HEInvocationOnTransform
