import Mettapedia.Languages.OpenTheory.Syntax
import Mathlib.Logic.Equiv.Basic

/-!
# Bijective names on the actual provenance-bearing source syntax

Constants, operators, type parameters and term variables have separate name
actions. Definition payloads are transformed recursively, including predicates
stored in type-operator provenance. This module concerns syntax and equality;
primitive-symbol laws and registered declaration transport are additional
obligations. No source checker is replaced by a comparison of printed names.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceNameAction

open Mettapedia.Languages.OpenTheory

structure Names where
  constants : Name ≃ Name
  operators : Name ≃ Name
  parameters : Name ≃ Name
  variables : Name ≃ Name

def Names.symm (names : Names) : Names :=
  ⟨names.constants.symm, names.operators.symm, names.parameters.symm, names.variables.symm⟩

@[simp] theorem Names.symm_constants (names : Names) : names.symm.constants = names.constants.symm := rfl
@[simp] theorem Names.symm_operators (names : Names) : names.symm.operators = names.operators.symm := rfl
@[simp] theorem Names.symm_parameters (names : Names) : names.symm.parameters = names.parameters.symm := rfl
@[simp] theorem Names.symm_variables (names : Names) : names.symm.variables = names.variables.symm := rfl

mutual
  def mapType (names : Names) : Ty → Ty
    | .var name => .var (names.parameters name)
    | .op operator arguments => .op (mapOperator names operator) (mapTypes names arguments)
  termination_by value => sizeOf value

  def mapTypes (names : Names) : List Ty → List Ty
    | [] => []
    | first :: later => mapType names first :: mapTypes names later
  termination_by values => sizeOf values

  def mapOperator (names : Names) : TypeOp → TypeOp
    | .mk name origin => .mk (names.operators name) (mapOperatorOrigin names origin)
  termination_by value => sizeOf value

  def mapOperatorOrigin (names : Names) : TypeOpProvenance → TypeOpProvenance
    | .undefined => .undefined
    | .defined predicate parameters =>
        .defined (mapTerm names predicate) (parameters.map names.parameters)
  termination_by value => sizeOf value

  def mapConstant (names : Names) : Const → Const
    | .mk name origin => .mk (names.constants name) (mapConstantOrigin names origin)
  termination_by value => sizeOf value

  def mapConstantOrigin (names : Names) : ConstProvenance → ConstProvenance
    | .undefined => .undefined
    | .defined body => .defined (mapTerm names body)
    | .abstraction operator => .abstraction (mapOperator names operator)
    | .representation operator => .representation (mapOperator names operator)
  termination_by value => sizeOf value

  def mapTerm (names : Names) : SourceTerm → SourceTerm
    | .const constant annotation => .const (mapConstant names constant) (mapType names annotation)
    | .var name annotation => .var (names.variables name) (mapType names annotation)
    | .app function argument => .app (mapTerm names function) (mapTerm names argument)
    | .abs name annotation body =>
        .abs (names.variables name) (mapType names annotation) (mapTerm names body)
  termination_by value => sizeOf value
end

mutual
  theorem type_roundtrip (names : Names) (value : Ty) :
      mapType names.symm (mapType names value) = value := by
    cases value <;> simp [mapType, operator_roundtrip, types_roundtrip]
  termination_by structural value

  theorem types_roundtrip (names : Names) (values : List Ty) :
      mapTypes names.symm (mapTypes names values) = values := by
    cases values <;> simp [mapTypes, type_roundtrip, types_roundtrip]
  termination_by structural values

  theorem operator_roundtrip (names : Names) (value : TypeOp) :
      mapOperator names.symm (mapOperator names value) = value := by
    cases value; simp [mapOperator, operatorOrigin_roundtrip]
  termination_by structural value

  theorem operatorOrigin_roundtrip (names : Names) (value : TypeOpProvenance) :
      mapOperatorOrigin names.symm (mapOperatorOrigin names value) = value := by
    cases value <;> simp [mapOperatorOrigin, term_roundtrip, List.map_map, Function.comp_def]
  termination_by structural value

  theorem constant_roundtrip (names : Names) (value : Const) :
      mapConstant names.symm (mapConstant names value) = value := by
    cases value; simp [mapConstant, constantOrigin_roundtrip]
  termination_by structural value

  theorem constantOrigin_roundtrip (names : Names) (value : ConstProvenance) :
      mapConstantOrigin names.symm (mapConstantOrigin names value) = value := by
    cases value <;> simp [mapConstantOrigin, term_roundtrip, operator_roundtrip]
  termination_by structural value

  theorem term_roundtrip (names : Names) (value : SourceTerm) :
      mapTerm names.symm (mapTerm names value) = value := by
    cases value <;> simp [mapTerm, constant_roundtrip, type_roundtrip, term_roundtrip]
  termination_by structural value
end

theorem type_injective (names : Names) : Function.Injective (mapType names) :=
  Function.LeftInverse.injective (type_roundtrip names)

theorem operator_injective (names : Names) : Function.Injective (mapOperator names) :=
  Function.LeftInverse.injective (operator_roundtrip names)

theorem constant_injective (names : Names) : Function.Injective (mapConstant names) :=
  Function.LeftInverse.injective (constant_roundtrip names)

theorem term_injective (names : Names) : Function.Injective (mapTerm names) :=
  Function.LeftInverse.injective (term_roundtrip names)

theorem type_comparison (names : Names) (first second : Ty) :
    Ty.same (mapType names first) (mapType names second) = Ty.same first second := by
  apply Bool.eq_iff_iff.mpr
  simp only [Ty.same_eq_true_iff, (type_injective names).eq_iff]

theorem constant_comparison (names : Names) (first second : Const) :
    Const.same (mapConstant names first) (mapConstant names second) = Const.same first second := by
  apply Bool.eq_iff_iff.mpr
  simp only [Const.same_eq_true_iff, (constant_injective names).eq_iff]

theorem operator_comparison (names : Names) (first second : TypeOp) :
    TypeOp.same (mapOperator names first) (mapOperator names second) = TypeOp.same first second := by
  apply Bool.eq_iff_iff.mpr
  simp only [TypeOp.same_eq_true_iff, (operator_injective names).eq_iff]

theorem term_comparison (names : Names) (first second : SourceTerm) :
    SourceTerm.same (mapTerm names first) (mapTerm names second) = SourceTerm.same first second := by
  apply Bool.eq_iff_iff.mpr
  simp only [SourceTerm.same_eq_true_iff, (term_injective names).eq_iff]

/-- Named source type checking recognizes this distinguished operator. A
bijective syntactic renaming alone need not preserve that recognition. -/
def FunctionFixed (names : Names) : Prop :=
  names.operators (Name.global "->") = Name.global "->"

theorem function_operator (names : Names) (fixed : FunctionFixed names) :
    mapOperator names TypeOp.function = TypeOp.function := by
  simp only [TypeOp.function, mapOperator, mapOperatorOrigin, FunctionFixed] at fixed ⊢
  rw [fixed]

theorem function_type (names : Names) (fixed : FunctionFixed names) (domain codomain : Ty) :
    mapType names (Ty.function domain codomain) =
      Ty.function (mapType names domain) (mapType names codomain) := by
  simp only [Ty.function, mapType, mapTypes, function_operator names fixed]

theorem function_view (names : Names) (fixed : FunctionFixed names) (type : Ty) :
    (mapType names type).destFunction? =
      type.destFunction?.map (fun pair => (mapType names pair.1, mapType names pair.2)) := by
  cases type with
  | var name => simp only [mapType, Ty.destFunction?, Option.map_none]
  | op operator arguments =>
      have same : TypeOp.same (mapOperator names operator) TypeOp.function =
          TypeOp.same operator TypeOp.function := by
        calc
          _ = TypeOp.same (mapOperator names operator) (mapOperator names TypeOp.function) :=
            congrArg (TypeOp.same (mapOperator names operator)) (function_operator names fixed).symm
          _ = _ := operator_comparison names operator TypeOp.function
      cases arguments with
      | nil => simp only [mapType, mapTypes, Ty.destFunction?, Option.map_none]
      | cons first rest =>
          cases rest with
          | nil => simp only [mapType, mapTypes, Ty.destFunction?, Option.map_none]
          | cons second rest =>
              cases rest with
              | nil =>
                  simp only [mapType, mapTypes, Ty.destFunction?, same]
                  cases TypeOp.same operator TypeOp.function <;> rfl
              | cons third rest => simp only [mapType, mapTypes, Ty.destFunction?, Option.map_none]

theorem inference (names : Names) (fixed : FunctionFixed names) (term : SourceTerm) :
    (mapTerm names term).inferType = term.inferType.map (mapType names) := by
  cases term with
  | const constant annotation => simp only [mapTerm, SourceTerm.inferType, Option.map_some]
  | var name annotation => simp only [mapTerm, SourceTerm.inferType, Option.map_some]
  | abs name annotation body =>
      simp only [mapTerm, SourceTerm.inferType, inference names fixed body]
      cases body.inferType <;> simp [function_type names fixed]
  | app function argument =>
      simp only [mapTerm, SourceTerm.inferType, inference names fixed function, inference names fixed argument]
      cases function.inferType with
      | none => rfl
      | some functionType =>
          cases argument.inferType with
          | none => rfl
          | some argumentType =>
              simp only [Option.map_some, bind, Option.bind, function_view names fixed]
              cases functionType.destFunction? with
              | none => rfl
              | some pair =>
                  simp only [Option.map_some, type_comparison]
                  cases Ty.same pair.1 argumentType <;> rfl
termination_by sizeOf term

theorem type_check_success (names : Names) (fixed : FunctionFixed names) (term : SourceTerm) :
    (mapTerm names term).check.isSome = term.check.isSome := by
  apply Bool.eq_iff_iff.mpr
  simp only [SourceTerm.check_isSome_iff, inference names fixed, Option.isSome_map]

namespace Controls

def unsafeArrow : Names :=
  ⟨Equiv.refl _, Equiv.swap (Name.global "->") (Name.global "arrow-as-data"),
    Equiv.refl _, Equiv.refl _⟩

def operand : Ty := .var (Name.global "A")
def functionAtom : SourceTerm :=
  .const (.mk (Name.global "f") .undefined) (Ty.function operand operand)
def argumentAtom : SourceTerm := .var (Name.global "x") operand
def application : SourceTerm := .app functionAtom argumentAtom

/-- Actual source type checking can be destroyed by an otherwise bijective
name action when it moves the distinguished function operator. -/
theorem moving_arrow_breaks_check :
    application.inferType = some operand ∧
      (mapTerm unsafeArrow application).inferType = none := by
  simp [application, functionAtom, argumentAtom, operand, SourceTerm.inferType,
    unsafeArrow, mapTerm, mapType, mapTypes, mapOperator, mapOperatorOrigin,
    mapConstant, mapConstantOrigin, Ty.function, Ty.destFunction?, TypeOp.function, Name.global]

def privateNames : Names :=
  ⟨Equiv.swap (Name.global "hidden-f") (Name.global "fresh-hidden-f"),
    Equiv.swap (Name.global "hidden-type") (Name.global "fresh-hidden-type"),
    Equiv.refl _, Equiv.swap (Name.global "x") (Name.global "fresh-x")⟩

theorem private_arrow_fixed : FunctionFixed privateNames := by
  unfold FunctionFixed privateNames
  decide +kernel

theorem private_application_typed :
    (mapTerm privateNames application).inferType = some operand := by
  rw [inference privateNames private_arrow_fixed]
  rw [moving_arrow_breaks_check.1]
  simp [mapType, operand, privateNames]

def privateOperand : Ty := .op (.mk (Name.global "hidden-type") .undefined) []

def privateIdentity : SourceTerm :=
  .abs (Name.global "x") privateOperand (.var (Name.global "x") privateOperand)

def privateConstant : Const := .mk (Name.global "hidden-f") (.defined privateIdentity)

/-- The payload participates in the action; keeping the old hidden type or
bound name inside provenance would violate this exact source identity. -/
theorem private_provenance_transported :
    mapConstant privateNames privateConstant =
      .mk (Name.global "fresh-hidden-f")
        (.defined (.abs (Name.global "fresh-x")
          (.op (.mk (Name.global "fresh-hidden-type") .undefined) [])
          (.var (Name.global "fresh-x")
            (.op (.mk (Name.global "fresh-hidden-type") .undefined) [])))) := by
  apply (Const.same_eq_true_iff _ _).mp
  decide +kernel

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceNameAction
