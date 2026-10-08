import Mettapedia.OSLF.Syntax.BindingClosedAuthoredPresentation
import Mettapedia.OSLF.Syntax.BindingClosedControls

/-!
# Genuine function-valued schema and equation-admission controls

A binary metavariable is evaluated on both ordered dependency arguments,
including beneath a two-name binding operator. A nontrivial tree model
satisfies an authored hold equation, while the original retained-hold model
rejects it. Distinct dependency positions and independently supplied functions
are distinguished by the actual generated schema interpretation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Binding.ClosedPresentation.SchemaControls

open _root_.CategoryTheory MonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open CategoricalBindingModel

abbrev binding := Controls.binding
abbrev Srt := Controls.Srt
abbrev Tree := Controls.Tree

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
    | .hold => ↾fun values => (show PUnit ⟶ Tree from values.1) PUnit.unit

def schema : List (MetaArity binding) := [([.name, .name], .code)]

def applyMeta {context : Ctx binding} (first second : Term (withMetas binding schema) context .name) :
    Term (withMetas binding schema) context .code :=
  .op (Sum.inr (.mk ⟨0, by decide⟩)) (.cons first (.cons second .nil))

def applied : Term (withMetas binding schema) [.name, .name] .code :=
  applyMeta (.var .zero) (.var (.succ .zero))

def swapped : Term (withMetas binding schema) [.name, .name] .code :=
  applyMeta (.var (.succ .zero)) (.var .zero)

def captured : Term (withMetas binding schema) [] .code :=
  .op (Sum.inl .capture) (.cons applied .nil)

def swappedCaptured : Term (withMetas binding schema) [] .code :=
  .op (Sum.inl .capture) (.cons swapped .nil)

def held : Term (withMetas binding schema) [.name, .name] .code :=
  .op (Sum.inl .hold) (.cons applied .nil)

def holdEquation : EqAxiom binding schema where
  ctx := [.name, .name]
  sort := .code
  lhs := held
  rhs := applied

def supplied (offset : Nat) : operations.power [.name, .name] .code :=
  ↾fun (values : Nat × Nat × PUnit) => .node values.1 (values.2.1 + offset)

def actual {context : Ctx binding} {sort : binding.Srt} (term : Term (withMetas binding schema) context sort) :
    Interpretation.ArrowValue (Type) :=
  ⟨operations.interpretation.functor.obj (SchemaExpressions.genericStage binding schema context),
    operations.interpretation.functor.obj (sortObject binding sort),
    operations.interpretation.functor.map (GeneratedCategory.classOf (SchemaExpressions.expression binding term))⟩

def read {context : Ctx binding} {sort : binding.Srt} (term : Term (withMetas binding schema) context sort)
    (environment : operations.context context) (metas : operations.family schema) :
    Option (operations.sort sort) :=
  (Interpretation.ArrowValue.readAt (some (actual term))
    (operations.context context ⊗ operations.family schema) (operations.sort sort)).map
      (fun arrow => arrow (environment, metas))

theorem read_generic {context : Ctx binding} {sort : binding.Srt}
    (term : Term (withMetas binding schema) context sort)
    (environment : operations.context context) (metas : operations.family schema) :
    read term environment metas = some (operations.model.generic schema term (environment, metas)) := by
  rw [read, actual, operations.schema_complete_readout, Interpretation.ArrowValue.readAt_supplied]
  rfl

theorem both_dependency_values (first second offset : Nat) :
    read applied (first, second, PUnit.unit) (supplied offset, PUnit.unit) =
      some (.node first (second + offset)) := by
  rw [read_generic]
  rfl

theorem complete_bound_function (offset : Nat) :
    read captured PUnit.unit (supplied offset, PUnit.unit) =
      some (.captured (fun first second => .node first (second + offset))) := by
  rw [read_generic]
  rfl

theorem complete_swapped_function (offset : Nat) :
    read swappedCaptured PUnit.unit (supplied offset, PUnit.unit) =
      some (.captured (fun first second => .node second (first + offset))) := by
  rw [read_generic]
  rfl

theorem bound_dependency_positions_remain_distinct :
    read captured PUnit.unit (supplied 0, PUnit.unit) ≠
      read swappedCaptured PUnit.unit (supplied 0, PUnit.unit) := by
  rw [complete_bound_function, complete_swapped_function]
  intro same
  have functions := Controls.Tree.captured.inj (Option.some.inj same)
  have values := congrArg (fun body : Nat → Nat → Tree => body 5 7) functions
  exact (by decide : (5 : Nat) ≠ 7) (Controls.Tree.node.inj values).1

theorem supplied_functions_remain_distinct :
    read applied ((5 : Nat), (7 : Nat), PUnit.unit) (supplied 11, PUnit.unit) ≠
      read applied ((5 : Nat), (7 : Nat), PUnit.unit) (supplied 13, PUnit.unit) := by
  rw [both_dependency_values, both_dependency_values]
  intro same
  exact (by decide : (18 : Nat) ≠ 20) (Controls.Tree.node.inj (Option.some.inj same)).2

theorem hold_schema_satisfied :
    operations.model.interp schema holdEquation.lhs = operations.model.interp schema holdEquation.rhs := by
  apply Model.ElemOver.ext
  funext Z metas environment
  rfl

def equationMetas (_ : Fin 1) := schema
def equationAt (_ : Fin 1) := holdEquation

theorem model_admitted :
    Interpretation.Realization (SchemaEquations.signature binding equationMetas equationAt)
      (SchemaEquations.assignment (Index := Fin 1) operations) :=
  (SchemaEquations.admission_iff equationMetas equationAt operations).mpr (fun _ => hold_schema_satisfied)

theorem actual_declared_schema_equation :
    (SchemaEquations.inclusion binding equationMetas equationAt).functor.map
        (GeneratedCategory.classOf (SchemaExpressions.expression binding held)) =
      (SchemaEquations.inclusion binding equationMetas equationAt).functor.map
        (GeneratedCategory.classOf (SchemaExpressions.expression binding applied)) :=
  SchemaEquations.authored_equation binding equationMetas equationAt ⟨0, by decide⟩

theorem holds_at_all_second_order_contexts :
    operations.model.Satisfies (SecondOrderContext.authoredEquationPresentation binding [holdEquation]) := by
  apply (operations.model.schema_family_iff_contextual [holdEquation]).mp
  intro index
  rcases index with ⟨index, bound⟩
  cases index with
  | zero => exact hold_schema_satisfied
  | succ index => simp at bound

theorem authored_list_model_admitted :
    Interpretation.Realization (AuthoredPresentation.signature.{0} [holdEquation])
      (SchemaEquations.assignment (Index := ULift.{0} (Fin 1)) operations) :=
  (AuthoredPresentation.admission_iff_contextual [holdEquation] operations).mpr
    holds_at_all_second_order_contexts

theorem retained_hold_model_rejects_schema :
    Controls.operations.model.interp schema holdEquation.lhs ≠
      Controls.operations.model.interp schema holdEquation.rhs := by
  intro same
  have value := congrArg (fun reading => reading.value PUnit (↾fun _ =>
    (show Controls.operations.power [.name, .name] .code from supplied 0, PUnit.unit))
      (fun _ position => match position with
        | .zero => ↾fun _ => (5 : Nat)
        | .succ .zero => ↾fun _ => (7 : Nat))) same
  have concrete := congrArg (fun arrow => arrow PUnit.unit) value
  cases concrete

theorem retained_hold_model_not_admitted :
    ¬ Interpretation.Realization (SchemaEquations.signature binding equationMetas equationAt)
      (SchemaEquations.assignment (Index := Fin 1) Controls.operations) := by
  intro admitted
  have satisfied := (SchemaEquations.admission_iff equationMetas equationAt Controls.operations).mp admitted
  exact retained_hold_model_rejects_schema (satisfied ⟨0, by decide⟩)

theorem original_constructor_category_does_not_equate_schema :
    GeneratedCategory.classOf (SchemaExpressions.expression.{0} binding held) ≠
      GeneratedCategory.classOf (SchemaExpressions.expression binding applied) := by
  intro same
  exact retained_hold_model_rejects_schema
    ((Controls.operations.schema_arrow_eq_iff held applied).mp
      (congrArg Controls.operations.interpretation.functor.map same))

end Mettapedia.OSLF.Binding.ClosedPresentation.SchemaControls
