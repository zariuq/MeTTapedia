import Mathlib.Data.List.Forall2
import Mathlib.Data.Finset.Basic

/-!
# Declarative tuple rules and flattened guard/gather plans

The source is a tuple-pattern rule. The realization reads coordinates in its
premise tuples, compares words, and gathers a conclusion. Word operations and
native instruction selection are independent of this matching layer.

Tags include the source constructor and space identity. Payload lengths are
logical arities; physical slot padding belongs to the layout boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.RuleTable

abbrev Word := BitVec 64

structure Tuple where
  tag : Nat
  fields : List Word
  deriving DecidableEq, Repr

inductive Atom where
  | variable (name : Nat)
  | literal (value : Word)
  deriving DecidableEq, Repr

structure Pattern where
  tag : Nat
  fields : List Atom
  deriving DecidableEq, Repr

abbrev Assignment := Nat → Word

def Atom.evaluate (assignment : Assignment) : Atom → Word
  | .variable name => assignment name
  | .literal value => value

def Pattern.instantiate (assignment : Assignment) (pattern : Pattern) : Tuple :=
  ⟨pattern.tag, pattern.fields.map (Atom.evaluate assignment)⟩

structure Rule where
  premises : List Pattern
  conclusion : Pattern
  deriving DecidableEq, Repr

/-- The declarative meaning retains the shared assignment across every tuple. -/
def Derives (rule : Rule) (premises : List Tuple) (conclusion : Tuple) : Prop :=
  ∃ assignment : Assignment,
    premises = rule.premises.map (Pattern.instantiate assignment) ∧
    conclusion = rule.conclusion.instantiate assignment

structure Coordinate where
  premise : Nat
  field : Nat
  deriving DecidableEq, Repr

def Coordinate.read (premises : List Tuple) (coordinate : Coordinate) : Option Word := do
  let tuple ← premises[coordinate.premise]?
  tuple.fields[coordinate.field]?

inductive Source where
  | field (coordinate : Coordinate)
  | literal (value : Word)
  deriving DecidableEq, Repr

def Source.read (premises : List Tuple) : Source → Option Word
  | .field coordinate => coordinate.read premises
  | .literal value => some value

structure Guard where
  left : Source
  right : Source
  deriving DecidableEq, Repr

def Guard.accepts (premises : List Tuple) (guard : Guard) : Bool :=
  match guard.left.read premises, guard.right.read premises with
  | some left, some right => left == right
  | _, _ => false

theorem Guard.accepts_iff (premises : List Tuple) (guard : Guard) :
    guard.accepts premises = true ↔
      ∃ value, guard.left.read premises = some value ∧ guard.right.read premises = some value := by
  unfold accepts
  cases left : guard.left.read premises with
  | none => simp
  | some a =>
      cases right : guard.right.read premises with
      | none => simp
      | some b =>
          simp only [beq_iff_eq, Option.some.injEq]
          exact ⟨fun equal => ⟨a, rfl, equal.symm⟩,
            fun ⟨_, ha, hb⟩ => ha.trans hb.symm⟩

structure Shape where
  tag : Nat
  arity : Nat
  deriving DecidableEq, Repr

def Tuple.shape (tuple : Tuple) : Shape := ⟨tuple.tag, tuple.fields.length⟩

def Pattern.shape (pattern : Pattern) : Shape := ⟨pattern.tag, pattern.fields.length⟩

structure Plan where
  inputs : List Shape
  guards : List Guard
  outputTag : Nat
  outputFields : List Source
  deriving DecidableEq, Repr

def gather (premises : List Tuple) : List Source → Option (List Word)
  | [] => some []
  | source :: rest => do
      let value ← source.read premises
      let later ← gather premises rest
      pure (value :: later)

def Plan.run (plan : Plan) (premises : List Tuple) : Option Tuple := do
  if premises.map Tuple.shape = plan.inputs then
    if plan.guards.all (Guard.accepts premises) then
      let fields ← gather premises plan.outputFields
      pure ⟨plan.outputTag, fields⟩
    else none
  else none

theorem gather_eq_some_iff (premises : List Tuple) (sources : List Source) (values : List Word) :
    gather premises sources = some values ↔
      List.Forall₂ (fun source value => source.read premises = some value) sources values := by
  induction sources generalizing values with
  | nil => cases values <;> simp [gather]
  | cons source rest ih =>
      cases valueEq : source.read premises with
      | none => simp [gather, valueEq, List.forall₂_cons_left_iff]
      | some value =>
          cases tailEq : gather premises rest <;> cases values <;>
            simp [gather, valueEq, tailEq, List.forall₂_cons, ← ih]

theorem Plan.run_eq_some_iff (plan : Plan) (premises : List Tuple) (output : Tuple) :
    plan.run premises = some output ↔
      premises.map Tuple.shape = plan.inputs ∧
      (∀ guard ∈ plan.guards, guard.accepts premises = true) ∧
      output.tag = plan.outputTag ∧
      gather premises plan.outputFields = some output.fields := by
  rw [← List.all_eq_true]
  cases output with
  | mk tag fields =>
    by_cases shape : premises.map Tuple.shape = plan.inputs
    · by_cases guards : plan.guards.all (Guard.accepts premises) = true
      · cases fieldsEq : gather premises plan.outputFields <;>
          simp [Plan.run, shape, guards, fieldsEq, Tuple.mk.injEq, eq_comm]
      · simp [Plan.run, shape, guards]
    · simp [Plan.run, shape]

namespace Controls

private def exampleRule : Rule :=
  ⟨[⟨1, [.variable 0, .variable 1]⟩, ⟨2, [.variable 1, .literal 0]⟩],
    ⟨3, [.variable 0]⟩⟩

private def examplePlan : Plan :=
  ⟨[⟨1, 2⟩, ⟨2, 2⟩],
    [⟨.field ⟨0, 1⟩, .field ⟨1, 0⟩⟩, ⟨.field ⟨1, 1⟩, .literal 0⟩],
    3, [.field ⟨0, 0⟩]⟩

example : examplePlan.run [⟨1, [7, 9]⟩, ⟨2, [9, 0]⟩] = some ⟨3, [7]⟩ := by decide

example : examplePlan.run [⟨1, [7, 9]⟩, ⟨2, [8, 0]⟩] = none := by decide

example : examplePlan.run [⟨1, [7, 9]⟩, ⟨2, [9, 1]⟩] = none := by decide

example : examplePlan.run [⟨1, [7, 9]⟩, ⟨4, [9, 0]⟩] = none := by decide

example : examplePlan.run [⟨1, [7, 9]⟩, ⟨2, [9]⟩] = none := by decide

example : Derives exampleRule [⟨1, [7, 9]⟩, ⟨2, [9, 0]⟩] ⟨3, [7]⟩ := by
  refine ⟨fun name => if name = 0 then 7 else 9, ?_, ?_⟩ <;>
    decide

end Controls

end Mettapedia.Machines.TIsa.RuleTable
