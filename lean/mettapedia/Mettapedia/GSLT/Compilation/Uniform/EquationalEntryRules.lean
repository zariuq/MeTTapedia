import Mettapedia.GSLT.Compilation.Uniform.StateRulesOnTheStep

/-!
# A single relational entry step with equation evidence

The first premise reads a representative at the named snapshot. The
second asks the ordinary entry question at that representative. Both
read the same world and scope. Neither receives the enclosing stack or
publication history; those pass through the rule structurally.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.EquationalEntryRules

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic (Tm inst)
open RuleSyntax.Machines (unknowns)
open RuleSyntax.ComputedConditions (Relations RelationStep RuleWithCondition Condition)
open StateRulesOnTheStep (packet pattern packet_eq_iff instantiate_packet instance_var)

structure Pending where
  world : Expr
  scope : Expr
  stack : Expr
  parents : Expr
  emitted : Expr
  task : Expr
  query : Expr

def request (tag : Nat) (p : Pending) : Expr :=
  packet tag [p.world, p.scope, p.stack, p.parents, p.emitted, p.task, p.query]

def entered (tag : Nat) (p : Pending) (captured : Expr) : Expr :=
  packet tag [p.world, p.scope, p.stack, p.parents, p.emitted, captured]

private def input (tag : Nat) : Tm := pattern tag ([0, 1, 2, 3, 4, 5, 6].map .var)
private def output (tag : Nat) : Tm := pattern tag ([0, 1, 2, 3, 4, 8].map .var)

private def equality (name : Nat) : Condition Nat Tm :=
  { name := name, arguments := [.var 0, .var 1, .var 6], value := .var 7 }

private def selection (name : Nat) : Condition Nat Tm :=
  { name := name, arguments := [.var 0, .var 1, .var 5, .var 7], value := .var 8 }

def rule (requestTag enteredTag equivalentAt selectAt : Nat) : RuleWithCondition Nat Tm :=
  StateRulesOnTheStep.rule (input requestTag) (output enteredTag) [equality equivalentAt, selection selectAt]

theorem input_tag {R : Relations} {tag enteredTag equivalentAt selectAt other : Nat} {parts : List Expr}
    {after : Multiset Expr} (step : RelationStep R (rule tag enteredTag equivalentAt selectAt)
      {packet other parts} after) : tag = other :=
  StateRulesOnTheStep.input_tag step

theorem restricted (tag enteredTag equivalentAt selectAt : Nat) :
    (rule tag enteredTag equivalentAt selectAt).RangeRestrictedWith := by
  apply StateRulesOnTheStep.restricted
  intro name member
  have inParts : name ∈ [0, 1, 2, 3, 4, 8] := by
    change name ∈ [0, 1, 2, 3, 4, 8] at member
    exact member
  by_cases last : name = 8
  · subst name
    exact Or.inr ⟨selection selectAt, List.mem_cons_of_mem _ List.mem_cons_self, List.mem_cons_self⟩
  · apply Or.inl
    change name ∈ [0, 1, 2, 3, 4, 5, 6]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inParts ⊢
    tauto

theorem exact_step (R : Relations) (tag enteredTag equivalentAt selectAt : Nat)
    (p : Pending) (after : Multiset Expr) :
    RelationStep R (rule tag enteredTag equivalentAt selectAt) {request tag p} after ↔
      ∃ representative captured, R equivalentAt [p.world, p.scope, p.query] representative ∧
        R selectAt [p.world, p.scope, p.task, representative] captured ∧
        after = {entered enteredTag p captured} := by
  rw [rule, StateRulesOnTheStep.instance_iff]
  constructor
  · rintro ⟨values, shape, checks, made⟩
    simp only [input, request, instantiate_packet, instance_var, List.map_cons, List.map_nil,
      packet_eq_iff, true_and, List.cons.injEq, and_true] at shape
    obtain ⟨world, scope, stack, parents, emitted, task, query⟩ := shape
    have eq := checks (equality equivalentAt) List.mem_cons_self
    have chosen := checks (selection selectAt) (List.mem_cons_of_mem _ List.mem_cons_self)
    refine ⟨values 7, values 8, ?_, ?_, ?_⟩
    · simpa only [equality, List.map_cons, List.map_nil, instance_var, world, scope, query] using eq
    · simpa only [selection, List.map_cons, List.map_nil, instance_var, world, scope, task] using chosen
    · simpa only [output, entered, instantiate_packet, List.map_cons, List.map_nil, instance_var,
        world, scope, stack, parents, emitted] using made
  · rintro ⟨representative, captured, equal, picked, rfl⟩
    let tape := [p.world, p.scope, p.stack, p.parents, p.emitted, p.task, p.query, representative, captured]
    let values := fun n : Nat => tape[n]?.getD (.sym 0)
    refine ⟨values, rfl, ?_, rfl⟩
    intro c kind
    rcases List.mem_cons.mp kind with rfl | remaining
    · exact equal
    · obtain rfl : c = selection selectAt := List.mem_singleton.mp remaining
      exact picked

end Mettapedia.GSLT.Compilation.Uniform.EquationalEntryRules
