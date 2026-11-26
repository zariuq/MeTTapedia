import Mettapedia.Languages.MeTTa.SpaceTheory.HEAtomEntry
import Mettapedia.Languages.MeTTa.SpaceTheory.HEContextEntry
import Mettapedia.Languages.MeTTa.SpaceTheory.HENativeOnTransform

/-!
# The six typed atom-entry rules on Transform

One schematic constructor generates the six rules. The primitive
condition presents independently licensed typed results. Its reply does
not include the old stack or publication history. The rule itself
adds the appropriate finite continuation prefix. Delivery sees only
the request; the other queries see its reached space.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEAtomOnTransform

open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result WorldEnvironment)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Task Continuation)
open Mettapedia.Languages.MeTTa.HE.ContextualData (taskData taskData_injective continuationData)
open HEFocused (Focus Parent)
open HEAtomEntry (Request Reply Licensed continuation)
open HENativeOnTransform
  (Presentation atom atom_injective commonFields workFields stackField parentsField historyField answerField returnAtom
    ordinaryAtom)
open Mettapedia.GSLT.Compilation.RootRewritesOnTheStep (appTerm symTerm inst_appTerm inst_symTerm)
open Mettapedia.GSLT.Compilation.Uniform
open StateRulesOnTheStep (fields fields_injective packet pattern packet_eq_iff instantiate_fields
  instantiate_packet instance_var)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic (Tm inst)
open RuleSyntax.ComputedConditions (Relations RelationStep Condition RuleWithCondition)

variable {Context World : Type}

inductive Branch where
  | deliver | cast | tuple | selected | fallback | failed
  deriving DecidableEq

def branches : List Branch := [.deliver, .cast, .tuple, .selected, .fallback, .failed]

theorem branch_mem (branch : Branch) : branch ∈ branches := by cases branch <;> simp [branches]

def branchOf : Reply → Branch
  | .deliver => .deliver
  | .cast _ => .cast
  | .tuple .. => .tuple
  | .selected .. => .selected
  | .fallback .. => .fallback
  | .failed .. => .failed

def Branch.port : Branch → Nat
  | .deliver => 3
  | .cast => 4
  | .tuple => 5
  | .selected => 6
  | .fallback => 7
  | .failed => 8

theorem port_injective : Function.Injective Branch.port := by
  intro a b same
  cases a <;> cases b <;> simp_all [Branch.port]

def Branch.outputTag : Branch → Nat
  | .deliver | .cast | .failed => 2
  | .tuple | .selected | .fallback => 9

def Branch.frameSlots : Branch → List Nat
  | .deliver | .cast => []
  | .selected | .failed => [7]
  | .tuple => [7, 8]
  | .fallback => [7, 8, 9]

def Branch.argumentSlots (b : Branch) : List Nat :=
  if b = .deliver then [5] else [0, 1, 5]

def requestAtom (code : Presentation Context World) (r : Request) (world : World) (scope : Context)
    (stack : List Continuation) (parents : List (Parent Context)) (emitted : List Result) : Expr :=
  packet 6 (workFields code r.task world scope stack parents emitted)

def payload (policy : Policy) (request : Request) (reply : Reply) : Expr :=
  match (continuation policy request reply).1 with
  | .work task => atom (taskData task)
  | .returning answers => answerField answers

def extraFrames (policy : Policy) (request : Request) (reply : Reply) : List Expr :=
  (continuation policy request reply).2.map (atom ∘ continuationData)

def replyData (policy : Policy) (request : Request) (reply : Reply) : Expr :=
  fields (payload policy request reply :: extraFrames policy request reply)

def outcomeAtom (code : Presentation Context World) (policy : Policy) (r : Request) (reply : Reply)
    (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) : Expr :=
  packet (branchOf reply).outputTag [atom (code.world world), atom (code.context scope),
    (extraFrames policy r reply).foldr Expr.app (stackField stack), parentsField code parents,
    historyField emitted, payload policy r reply]

theorem outcome_shape (code : Presentation Context World) (policy : Policy) (r : Request) (reply : Reply)
    (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) :
    let updated := (continuation policy r reply).2 ++ stack
    outcomeAtom code policy r reply world scope stack parents emitted =
      match (continuation policy r reply).1 with
      | .work task => ordinaryAtom code task world scope updated parents emitted
      | .returning answers => returnAtom code world scope answers updated parents emitted := by
  cases reply <;> rfl

theorem work_outcome_is_ordinary (policy : Policy) (r : Request) (reply : Reply) {task : Task}
    (shape : (continuation policy r reply).1 = .work task) :
    HEFocused.NativeRequest.recognize task = none ∧ HEContextEntry.Request.recognize task = none ∧
      HEAtomEntry.Request.recognize task = none := by
  cases reply <;> cases shape <;> exact ⟨rfl, rfl, rfl⟩

def arguments (code : Presentation Context World) (b : Branch) (r : Request) (w : World) (c : Context) : List Expr :=
  if b = .deliver then [atom (taskData r.task)]
    else [atom (code.world w), atom (code.context c), atom (taskData r.task)]

def read (code : Presentation Context World) (env : WorldEnvironment Context World) (policy : Policy)
    (b : Branch) (r : Request) (reply : Reply) (input : List Expr) : Prop :=
  if b = .deliver then
    input = [atom (taskData r.task)] ∧ r.action policy .deliver
  else ∃ w c, input = arguments code b r w c ∧ Licensed env.arguments (env.view w c) env.lookup policy r reply

def operations (code : Presentation Context World) (env : WorldEnvironment Context World) (policy : Policy) :
    Relations :=
  fun name input data =>
    ∃ b r reply, name = Branch.port b ∧ branchOf reply = b ∧
      read code env policy b r reply input ∧ data = replyData policy r reply

private theorem request_field_eq {left right : Request}
    (same : atom (taskData left.task) = atom (taskData right.task)) : left = right :=
  Request.task_injective (taskData_injective (atom_injective same))

private theorem only_delivery (reply : Reply) (tag : branchOf reply = .deliver) : reply = .deliver := by
  cases reply <;> simp_all [branchOf]

theorem operation_exact (code : Presentation Context World) (env : WorldEnvironment Context World)
    (policy : Policy) (b : Branch) (r : Request) (world : World) (scope : Context) (data : Expr) :
    operations code env policy b.port (arguments code b r world scope) data ↔
      ∃ reply, branchOf reply = b ∧ Licensed env.arguments (env.view world scope) env.lookup policy r reply ∧
        data = replyData policy r reply := by
  constructor
  · rintro ⟨actual, request, reply, name, branch, allowed, result⟩
    have sameBranch : actual = b := (port_injective name).symm
    rw [sameBranch] at branch allowed
    by_cases delivers : b = .deliver
    · have only := only_delivery reply (branch.trans delivers)
      subst reply
      simp only [read, arguments, if_pos delivers] at allowed
      obtain rfl := request_field_eq (List.cons.inj allowed.1).1
      exact ⟨.deliver, branch, ⟨allowed.2, trivial⟩, result⟩
    · simp only [read, if_neg delivers] at allowed
      obtain ⟨w, c, asked, license⟩ := allowed
      simp only [arguments, if_neg delivers] at asked
      have sameW := (List.cons.inj asked).1
      have sameC := (List.cons.inj (List.cons.inj asked).2).1
      have sameR := (List.cons.inj (List.cons.inj (List.cons.inj asked).2).2).1
      obtain rfl := code.world_injective (atom_injective sameW)
      obtain rfl := code.context_injective (atom_injective sameC)
      obtain rfl := request_field_eq sameR
      exact ⟨reply, branch, license, result⟩
  · rintro ⟨reply, branch, license, result⟩
    refine ⟨b, r, reply, rfl, branch, ?_, result⟩
    by_cases delivers : b = .deliver
    · have only := only_delivery reply (branch.trans delivers)
      subst reply
      rw [read, if_pos delivers, arguments, if_pos delivers]
      exact ⟨rfl, license.1⟩
    · rw [read, if_neg delivers]
      exact ⟨world, scope, rfl, license⟩

private def varList (keys : List Nat) : List Tm := keys.map .var

private def taken : Tm := pattern 6 (varList [0, 1, 2, 3, 4, 5])

private def made (b : Branch) : Tm :=
  pattern b.outputTag [.var 0, .var 1, (varList b.frameSlots).foldr appTerm (.var 2), .var 3, .var 4, .var 6]

private def ask (b : Branch) : Condition Nat Tm :=
  { name := b.port, arguments := varList b.argumentSlots,
    value := (varList (6 :: b.frameSlots)).foldr appTerm (symTerm 0) }

def rule (b : Branch) : RuleWithCondition Nat Tm := StateRulesOnTheStep.rule taken (made b) [ask b]

def rules : List (RuleWithCondition Nat Tm) := branches.map rule

theorem asks_port (b : Branch) (c : Condition Nat Tm) (member : c ∈ (rule b).conditions) : c.name = b.port := by
  obtain rfl : c = ask b := List.mem_singleton.mp member
  rfl

theorem input_tag {rel : Relations} {b : Branch} {tag : Nat} {items : List Expr} {after : Multiset Expr}
    (step : RelationStep rel (rule b) {packet tag items} after) : 6 = tag :=
  StateRulesOnTheStep.input_tag step

theorem rule_restricted (b : Branch) : (rule b).RangeRestrictedWith := by
  apply StateRulesOnTheStep.restricted
  intro x member
  let ends := RuleSyntax.Machines.unknowns (made b)
  let bound := RuleSyntax.Machines.unknowns taken ++ RuleSyntax.Machines.unknowns (ask b).value
  have included : ends.all bound.contains = true := by cases b <;> decide +kernel
  have present : x ∈ bound := List.contains_iff_mem.mp ((List.all_eq_true.mp included) x member)
  rcases List.mem_append.mp present with available | produced
  · exact Or.inl available
  · exact Or.inr ⟨ask b, List.mem_cons_self, produced⟩

private theorem instantiated_vars (v : Nat → Expr) (keys : List Nat) :
    (varList keys).map (inst v) = keys.map v := by
  induction keys with
  | nil => rfl
  | cons first rest ih =>
    simp only [varList, List.map_cons, instance_var] at ih ⊢
    rw [ih]

private theorem instantiated_open (v : Nat → Expr) (keys : List Nat) :
    inst v ((varList keys).foldr appTerm (.var 2)) = (keys.map v).foldr Expr.app (v 2) := by
  induction keys with
  | nil => rfl
  | cons first rest ih =>
    simp only [varList, List.map_cons, List.foldr_cons, inst_appTerm, instance_var] at ih ⊢
    rw [ih]

theorem rule_exact (code : Presentation Context World) (env : WorldEnvironment Context World) (policy : Policy)
    (b : Branch) (r : Request) (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) (after : Multiset Expr) :
    RelationStep (operations code env policy) (rule b) {requestAtom code r world scope stack parents emitted} after ↔
      ∃ reply, branchOf reply = b ∧ Licensed env.arguments (env.view world scope) env.lookup policy r reply ∧
        after = {outcomeAtom code policy r reply world scope stack parents emitted} := by
  rw [rule, StateRulesOnTheStep.instance_iff]
  constructor
  · rintro ⟨v, matched, conditions, out⟩
    simp only [taken, instantiate_packet, instantiated_vars, requestAtom, workFields, commonFields,
      List.cons_append, List.nil_append, List.map_cons, List.map_nil, packet_eq_iff, true_and, List.cons.injEq,
      and_true] at matched
    obtain ⟨w, c, k, p, h, t⟩ := matched
    have reading := conditions (ask b) List.mem_cons_self
    have computed : operations code env policy b.port (arguments code b r world scope)
        (fields (v 6 :: b.frameSlots.map v)) := by
      simp only [ask, instantiate_fields, instantiated_vars, List.map_cons] at reading
      by_cases del : b = .deliver
      · simpa [arguments, Branch.argumentSlots, del, t] using reading
      · simpa [arguments, Branch.argumentSlots, del, w, c, t] using reading
    obtain ⟨reply, branch, licensed, packed⟩ := (operation_exact code env policy b r world scope _).mp computed
    obtain ⟨body, frame⟩ := List.cons.inj (fields_injective packed)
    refine ⟨reply, branch, licensed, ?_⟩
    simpa only [made, instantiate_packet, List.map_cons, List.map_nil, instance_var, instantiated_open,
      w, c, k, p, h, body, frame, outcomeAtom, branch] using out
  · rintro ⟨reply, branch, licensed, rfl⟩
    subst b
    let slots := workFields code r.task world scope stack parents emitted ++
      payload policy r reply :: extraFrames policy r reply
    let v := fun n : Nat => slots[n]?.getD (.sym 0)
    refine ⟨v, ?_, ?_, ?_⟩
    · simp [taken, instantiate_packet, instantiated_vars, requestAtom, workFields, commonFields, slots, v]
    · intro cond member
      obtain rfl : cond = ask (branchOf reply) := List.mem_singleton.mp member
      have reads := (operation_exact code env policy (branchOf reply) r world scope (replyData policy r reply)).mpr
        ⟨reply, rfl, licensed, rfl⟩
      cases reply <;>
        simpa [ask, instantiate_fields, instantiated_vars, instance_var, varList, slots, workFields, commonFields, v,
          branchOf, Branch.argumentSlots, Branch.frameSlots, replyData, extraFrames,
          continuation, arguments, fields] using reads
    · cases reply <;> simp [made, instantiate_packet, instantiated_open, instance_var, slots, workFields,
        commonFields, v, branchOf, Branch.frameSlots, outcomeAtom, extraFrames, continuation]

end Mettapedia.Languages.MeTTa.SpaceTheory.HEAtomOnTransform
