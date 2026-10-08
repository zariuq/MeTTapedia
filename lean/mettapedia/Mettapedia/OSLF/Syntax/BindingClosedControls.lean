import Mettapedia.OSLF.Syntax.BindingClosedSubstitution
import Mettapedia.OSLF.Syntax.BindingClosedUniversal
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Complete generic binding readouts and positional controls

A two-sort signature has nullary operators, unbound arguments and an
operator binding two names. Its independent target algebra retains the whole
future function. The actual generated functor is exercised on open terms,
repeated same-sort variables and substitution beneath both binders.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Binding.ClosedPresentation.Controls

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation

inductive Srt where
  | name
  | code
  deriving DecidableEq

inductive Op : Srt → Type where
  | literal (value : Nat) : Op .name
  | node : Op .code
  | capture : Op .code
  | hold : Op .code

def binding : Mettapedia.OSLF.Binding.Signature where
  Srt := Srt
  Op := Op
  arity
    | .literal _ => []
    | .node => [([], .name), ([], .name)]
    | .capture => [([.name, .name], .code)]
    | .hold => [([], .code)]

inductive Tree where
  | node (first second : Nat)
  | captured (body : Nat → Nat → Tree)
  | held (body : Tree)

def operations : Operations binding (Type) where
  sort
    | .name => Nat
    | .code => Tree
  operation
    | .literal value => ↾fun _ => value
    | .node => ↾fun values => .node
        ((show PUnit ⟶ Nat from values.1) PUnit.unit)
        ((show PUnit ⟶ Nat from values.2.1) PUnit.unit)
    | .capture => ↾fun values => .captured (fun first second =>
        (show (Nat × Nat × PUnit) ⟶ Tree from values.1) (first, second, PUnit.unit))
    | .hold => ↾fun values => .held ((show PUnit ⟶ Tree from values.1) PUnit.unit)

def node {context : Ctx binding} (first second : Term binding context .name) :
    Term binding context .code := .op .node (.cons first (.cons second .nil))

def body : Term binding [.name, .name, .name] .code :=
  node (.var .zero) (.var (.succ (.succ .zero)))

def otherBody : Term binding [.name, .name, .name] .code :=
  node (.var (.succ .zero)) (.var (.succ (.succ .zero)))

def captured : Term binding [.name] .code := .op .capture (.cons body .nil)
def otherCaptured : Term binding [.name] .code := .op .capture (.cons otherBody .nil)

def actual {context : Ctx binding} {sort : Srt} (term : Term binding context sort) : ArrowValue (Type) :=
  ⟨operations.interpretation.functor.obj (contextObject binding context),
    operations.interpretation.functor.obj (sortObject binding sort),
    operations.interpretation.functor.map (termArrow binding term)⟩

def read {context : Ctx binding} {sort : Srt} (term : Term binding context sort)
    (environment : operations.context context) : Option (operations.sort sort) :=
  (ArrowValue.readAt (some (actual term)) (operations.context context) (operations.sort sort)).map
    (fun arrow => arrow environment)

theorem read_meaning {context : Ctx binding} {sort : Srt} (term : Term binding context sort)
    (environment : operations.context context) : read term environment = some (operations.meaning term environment) := by
  rw [read, actual, operations.term_complete_readout, ArrowValue.readAt_supplied]
  rfl

theorem complete_two_binder_readout (ambient : Nat) :
    read captured (ambient, PUnit.unit) = some (.captured (fun first _ => .node first ambient)) := by
  rw [read_meaning]
  rfl

theorem complete_other_position_readout (ambient : Nat) :
    read otherCaptured (ambient, PUnit.unit) = some (.captured (fun _ second => .node second ambient)) := by
  rw [read_meaning]
  rfl

theorem same_sort_binders_are_not_exchanged : read captured ((13 : Nat), PUnit.unit) ≠ read otherCaptured ((13 : Nat), PUnit.unit) := by
  rw [complete_two_binder_readout, complete_other_position_readout]
  intro same
  have functions := Tree.captured.inj (Option.some.inj same)
  have values := congrArg (fun body : Nat → Nat → Tree => body 5 7) functions
  exact (by decide : (5 : Nat) ≠ 7) (Tree.node.inj values).1

theorem ambient_variable_is_retained : read captured ((13 : Nat), PUnit.unit) ≠ read captured ((17 : Nat), PUnit.unit) := by
  rw [complete_two_binder_readout, complete_two_binder_readout]
  intro same
  have functions := Tree.captured.inj (Option.some.inj same)
  have values := congrArg (fun body : Nat → Nat → Tree => body 5 7) functions
  exact (by decide : (13 : Nat) ≠ 17) (Tree.node.inj values).2

def replacement : Sub binding [.name] [] := fun _ position => match position with
  | .zero => .op (.literal 23) .nil

theorem complete_substitution_beneath_two_binders :
    read (bind replacement captured) PUnit.unit = some (.captured (fun first _ => .node first 23)) := by
  rw [read_meaning, operations.meaning_substitution]
  rfl

theorem nullary_operator_retains_its_value :
    read (Term.op (S := binding) (.literal 29) (Args.nil (Γ := []))) PUnit.unit = some (29 : Nat) := by
  rw [read_meaning]
  rfl

theorem unbound_argument_is_applied :
    read (Term.op (S := binding) .hold (.cons captured .nil)) ((13 : Nat), PUnit.unit) =
      some (.held (.captured (fun first _ => .node first 13))) := by
  rw [read_meaning]
  rfl

theorem nullary_values_do_not_collapse :
    read (Term.op (S := binding) (.literal 29) (Args.nil (Γ := []))) PUnit.unit ≠
      read (Term.op (S := binding) (.literal 31) (Args.nil (Γ := []))) PUnit.unit := by
  rw [nullary_operator_retains_its_value, read_meaning]
  intro same
  exact (by decide : (29 : Nat) ≠ 31) (Option.some.inj same)

end Mettapedia.OSLF.Binding.ClosedPresentation.Controls
