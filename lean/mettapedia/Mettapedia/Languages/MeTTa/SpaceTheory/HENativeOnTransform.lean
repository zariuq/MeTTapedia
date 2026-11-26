import Mettapedia.Languages.MeTTa.SpaceTheory.HEFocused
import Mettapedia.Languages.MeTTa.SpaceTheory.HESnapshotEntry
import Mettapedia.Languages.MeTTa.HE.ContextualData
import Mettapedia.Languages.MeTTa.OSLFCore.Bridge
import Mettapedia.GSLT.Compilation.Uniform.StateRulesOnTheStep

/-!
# A focused HE native invocation on Transform

The rule takes a focused request and makes its returned batch, with the
new world supplied by one primitive condition. The condition asks only
for the actual host operation, not for a source transition or recursive
evaluation. The rule itself retains the context, stack, parents, and
publication history. Unrelated Transform rules are not part of this local
program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HENativeOnTransform

open Mettapedia.GSLT.Compilation.RootRewritesOnTheStep (encode encode_injective appTerm inst_appTerm)
open Mettapedia.GSLT.Compilation.Uniform
open StateRulesOnTheStep (packet packet_eq_iff pattern instantiate_packet instance_var spine spine_injective)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Frame Result WorldServices)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Continuation Task)
open Mettapedia.Languages.MeTTa.HE.ContextualData
open HEFocused (Parent NativeRequest)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic (Tm inst)
open RuleSyntax.Machines (unknowns)
open RuleSyntax.ComputedConditions

structure Presentation (Context World : Type) where
  context : Context → Atom
  world : World → Atom
  context_injective : Function.Injective context
  world_injective : Function.Injective world

variable {Context World : Type}

def atom (value : Atom) : Expr := encode (GroundData.encode value)

theorem atom_injective : Function.Injective atom :=
  encode_injective.comp GroundData.encode_injective

def stackField : List Continuation → Expr := spine (atom ∘ continuationData)

@[simp] theorem stackField_nil : stackField [] = .sym 0 := rfl

theorem stackField_injective : Function.Injective stackField :=
  spine_injective (atom_injective.comp continuationData_injective)

def parentField (code : Presentation Context World) (parent : Parent Context) : Expr :=
  .app (atom (code.context parent.scope)) (stackField parent.stack)

theorem parentField_injective (code : Presentation Context World) :
    Function.Injective (parentField code) := by
  intro p q equal
  cases p
  cases q
  simp_all [parentField, atom_injective.eq_iff, code.context_injective.eq_iff, stackField_injective.eq_iff]

def parentsField (code : Presentation Context World) : List (Parent Context) → Expr :=
  spine (parentField code)

@[simp] theorem parentsField_nil (code : Presentation Context World) : parentsField code [] = .sym 0 := rfl

theorem parentsField_injective (code : Presentation Context World) :
    Function.Injective (parentsField code) := spine_injective (parentField_injective code)

def answerField : List Result → Expr := spine (atom ∘ resultData)

theorem answerField_injective : Function.Injective answerField :=
  spine_injective (atom_injective.comp resultData_injective)

/-- Published answers are read in source order. Their on-step view is
reversed so one publication adds one cons without inspecting the prefix. -/
def historyField (published : List Result) : Expr := answerField published.reverse

theorem historyField_injective : Function.Injective historyField := by
  intro first second same
  exact List.reverse_injective (answerField_injective same)

@[simp] theorem historyField_emit (published : List Result) (next : Result) :
    historyField (published ++ [next]) = .app (atom (resultData next)) (historyField published) := by
  simp [historyField, answerField, List.reverse_append]

def commonFields (code : Presentation Context World)
    (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) : List Expr :=
  [atom (code.world world), atom (code.context scope), stackField stack,
    parentsField code parents, historyField emitted]

def workFields (code : Presentation Context World) (task : Task)
    (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) (extras : List Expr := []) : List Expr :=
  commonFields code world scope stack parents emitted ++ atom (taskData task) :: extras

/-- Every typed atom request uses the same entry tag, independent of
its type, readiness, and current declarations. -/
def ordinaryTag : Task → Nat
  | .atom .. => 6
  | .call .. | .invocation .. | .equations .. | .invocationEquations .. => 7
  | .body .. | .boundary .. | .boundaryBatch .. | .returned .. => 8
  | .tuple .. | .branches .. | .arguments .. | .argumentBranches ..
  | .function .. | .functionBranches .. | .invocations .. | .calls .. => 9
  | task => if HESnapshotEntry.covered task then 10 else 3

theorem ordinaryTag_not_return (task : Task) : ordinaryTag task ≠ 2 := by
  cases task <;> simp [ordinaryTag, HESnapshotEntry.covered]
  case minimal live scope caller value frame =>
    by_cases kind : HESnapshotEntry.isInstruction value = true <;> simp [kind]

def ordinaryAtom (code : Presentation Context World) (task : Task) (world : World) (scope : Context)
    (stack : List Continuation) (parents : List (Parent Context)) (emitted : List Result) : Expr :=
  packet (ordinaryTag task) (workFields code task world scope stack parents emitted)

def nativeExtras (request : NativeRequest) : List Expr :=
  [atom request.name.erase, atom request.operation.erase, atom request.argument.erase, atom (frameData request.frame)]

def requestFields (code : Presentation Context World) (request : NativeRequest)
    (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) : List Expr :=
  workFields code request.task world scope stack parents emitted (nativeExtras request)

def requestAtom (code : Presentation Context World) (request : NativeRequest)
    (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) : Expr :=
  packet 1 (requestFields code request world scope stack parents emitted)

def returnAtom (code : Presentation Context World) (world : World) (scope : Context)
    (answers : List Result) (stack : List Continuation) (parents : List (Parent Context))
    (emitted : List Result) : Expr :=
  packet 2 (commonFields code world scope stack parents emitted ++ [answerField answers])

/-- Only the primitive input and output positions are part of this graph.
In particular it cannot supply a caller continuation or published result. -/
def operations (code : Presentation Context World) (services : WorldServices Context World) : Relations :=
  fun name arguments reply => name = 0 ∧
    ∃ (scope : Context) (world : World) (requested operation argument : Atom)
      (frame : Frame) (answers : List Result) (next : World),
      arguments = [atom (code.context scope), atom (code.world world), atom requested,
        atom operation, atom argument, atom (frameData frame)] ∧
      services.nativeCall scope world requested operation argument frame answers next ∧
      reply = .app (atom (code.world next)) (answerField answers)

private def taken : Tm :=
  pattern 1 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9].map .var)

private def made : Tm := pattern 2 ([10, 1, 2, 3, 4, 11].map .var)

private def ask : Condition Nat Tm :=
  { name := 0, arguments := [1, 0, 6, 7, 8, 9].map .var, value := appTerm (.var 10) (.var 11) }

def rule : RuleWithCondition Nat Tm := StateRulesOnTheStep.rule taken made [ask]

theorem input_tag {ops : Relations} {tag : Nat} {items : List Expr} {after : Multiset Expr}
    (step : RelationStep ops rule {packet tag items} after) : 1 = tag :=
  StateRulesOnTheStep.input_tag step

theorem asks_native (c : Condition Nat Tm) (member : c ∈ rule.conditions) : c.name = 0 := by
  obtain rfl : c = ask := List.mem_singleton.mp member
  rfl

/-- The actual rule has exactly the primitive host's alternatives from a
represented request, even when the host changes the shared world. -/
theorem native_rewrite_iff (code : Presentation Context World) (services : WorldServices Context World)
    (request : NativeRequest) (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) (after : Multiset Expr) :
    RelationStep (operations code services) rule {requestAtom code request world scope stack parents emitted} after ↔
      ∃ answers updated, services.nativeCall scope world request.name.erase request.operation.erase
        request.argument.erase request.frame answers updated ∧
        after = {returnAtom code updated scope answers stack parents emitted} := by
  rw [rule, StateRulesOnTheStep.instance_iff]
  constructor
  · rintro ⟨values, equal, conditions, result⟩
    have actualFields := ((packet_eq_iff 1 1 _ _).mp
      (show packet 1 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9].map values) =
        requestAtom code request world scope stack parents emitted by
        simpa only [taken, instantiate_packet, List.map_map, Function.comp_def, instance_var,
          List.map_cons, List.map_nil] using equal)).2
    simp only [requestFields, workFields, commonFields, nativeExtras, List.cons_append, List.nil_append,
      List.map_cons, List.map_nil, List.cons.injEq, and_true] at actualFields
    rcases actualFields with ⟨e0, e1, e2, e3, e4, _, e6, e7, e8, e9⟩
    have chosen := conditions ask List.mem_cons_self
    simp only [ask, List.map_cons, List.map_nil, instance_var, inst_appTerm, e1, e0, e6, e7, e8, e9] at chosen
    obtain ⟨_, foundScope, foundWorld, name, operation, argument, frame, answers, updated, inputs, fired, pair⟩ :=
      chosen
    simp only [List.cons.injEq, and_true, atom_injective.eq_iff, code.context_injective.eq_iff,
      code.world_injective.eq_iff, frameData_injective.eq_iff] at inputs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := inputs
    have replies := Expr.app.inj pair
    refine ⟨answers, updated, fired, ?_⟩
    simpa only [returnAtom, commonFields, List.cons_append, List.nil_append, made, instantiate_packet,
      List.map_cons, List.map_nil, instance_var,
      e1, e2, e3, e4, replies.1, replies.2] using result
  · rintro ⟨answers, updated, fired, rfl⟩
    let all := requestFields code request world scope stack parents emitted ++
      [atom (code.world updated), answerField answers]
    let values := fun n : Nat => all[n]?.getD (.sym 0)
    refine ⟨values, ?_, ?_, ?_⟩
    · simp [taken, instantiate_packet, instance_var, values, all, requestAtom, requestFields,
        workFields, commonFields, nativeExtras]
    · intro condition member
      obtain rfl : condition = ask := List.mem_singleton.mp member
      refine ⟨rfl, scope, world, request.name.erase, request.operation.erase, request.argument.erase,
        request.frame, answers, updated, ?_, fired, ?_⟩
      all_goals simp [ask, instance_var, values, all, requestFields, workFields, commonFields, nativeExtras]
    · simp [made, instantiate_packet, instance_var, values, all, returnAtom, requestFields,
        workFields, commonFields, nativeExtras]

theorem rule_restricted : rule.RangeRestrictedWith := by
  unfold rule
  apply StateRulesOnTheStep.restricted
  intro x madeName
  have inputs : unknowns taken = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := rfl
  have outputs : unknowns made = [10, 1, 2, 3, 4, 11] := rfl
  have response : unknowns ask.value = [10, 11] := rfl
  rw [outputs] at madeName
  by_cases matched : x ∈ unknowns taken
  · exact Or.inl matched
  · refine Or.inr ⟨ask, List.mem_cons_self, ?_⟩
    rw [inputs] at matched
    rw [response]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at madeName matched ⊢
    tauto

end Mettapedia.Languages.MeTTa.SpaceTheory.HENativeOnTransform
