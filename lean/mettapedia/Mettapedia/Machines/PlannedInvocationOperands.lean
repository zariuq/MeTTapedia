import Mettapedia.Machines.ContextualInvocation
import Mettapedia.Languages.MeTTa.SubstitutionAlgebra

/-!
# Dynamic invocation from program-owned operand templates

The reference instantiates the whole application before inspecting its fields.
The target reads the head and then iterates over the operand templates, keeping
their values in an ordered span. Only a syntax/data observer constructs the
application. The substitution is an already resolved binding image; substituting
a ready value does not evaluate it or descend into that value again.

This covers first-order template instantiation and the common contextual entry
that consumes its fields. Private callable/list encodings, alias dereferencing,
template compilation, native admission and borrowed-pointer lifetimes retain
their separate correspondence obligations. No allocation or timing bound follows
from the mathematical absence of an application constructor in the target.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PlannedInvocationOperands

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Subst subst)

def assemble (environment : Subst) : List Atom → List Atom → List Atom
  | [], reversed => reversed.reverse
  | operand :: rest, reversed => assemble environment rest (subst environment operand :: reversed)

theorem assemble_exact (environment : Subst) (operands reversed : List Atom) :
    assemble environment operands reversed = reversed.reverse ++ operands.map (subst environment) := by
  induction operands generalizing reversed with
  | nil => simp [assemble]
  | cons first rest ih =>
    simp [assemble, ih, List.reverse_cons, List.append_assoc]

def project (environment : Subst) (head : Atom) (operands : List Atom) :
    NativeCallReturn.Arguments.Input Atom :=
  ⟨subst environment head, #[], (assemble environment operands []).toArray⟩

def reference (environment : Subst) (head : Atom) (operands : List Atom) : Atom :=
  subst environment (.expression (head :: operands))

theorem substituted_fields (environment : Subst) (operands : List Atom) :
    subst.substList environment operands = operands.map (subst environment) := by
  induction operands with
  | nil => rfl
  | cons first rest ih => simp [subst.substList, ih]

def fields : Atom → Option (Atom × List Atom)
  | .expression (head :: operands) => some (head, operands)
  | _ => none

theorem project_arguments (environment : Subst) (head : Atom) (operands : List Atom) :
    (project environment head operands).arguments = operands.map (subst environment) := by
  simp [project, assemble_exact, NativeCallReturn.Arguments.Input.arguments]

theorem project_arity (environment : Subst) (head : Atom) (operands : List Atom) :
    (project environment head operands).arity = operands.length := by
  rw [← NativeCallReturn.Arguments.Input.arguments_length, project_arguments, List.length_map]

theorem materialization_refines (environment : Subst) (head : Atom) (operands : List Atom) :
    .expression ((project environment head operands).head ::
      (project environment head operands).arguments) = reference environment head operands := by
  rw [project_arguments]
  simp [project, reference, subst, substituted_fields]

theorem fields_refine (environment : Subst) (head : Atom) (operands : List Atom) :
    fields (reference environment head operands) =
      some ((project environment head operands).head,
        (project environment head operands).arguments) := by
  rw [← materialization_refines]
  rfl

theorem read_refines (environment : Subst) (head : Atom) (operands : List Atom) (index : Nat) :
    (project environment head operands).read index =
      (operands.map (subst environment))[index]? := by
  rw [NativeCallReturn.Arguments.Input.read_refines, project_arguments]

theorem repeated_occurrences (environment : Subst) (head operand : Atom) :
    (project environment head [operand, operand]).arguments =
      [subst environment operand, subst environment operand] := by
  simp [project_arguments]

def sourceEnter {Result : Type} (enter : Atom → List Atom → Result)
    (environment : Subst) (head : Atom) (operands : List Atom) : Option Result :=
  (fields (reference environment head operands)).map fun (readyHead, readyOperands) =>
    enter readyHead readyOperands

def targetEnter {Result : Type} (enter : Atom → List Atom → Result)
    (environment : Subst) (head : Atom) (operands : List Atom) : Result :=
  let invocation := project environment head operands
  enter invocation.head invocation.arguments

theorem entry_refines {Result : Type} (enter : Atom → List Atom → Result)
    (environment : Subst) (head : Atom) (operands : List Atom) :
    sourceEnter enter environment head operands = some (targetEnter enter environment head operands) := by
  simp [sourceEnter, targetEnter, fields_refine]

section Kernel

variable {Value Call Effect Fault Delay Suspension Context World Worker : Type}

abbrev Code := ContextualCBPV.Code Value Call Effect Fault Delay Suspension

variable (sem : ContextualCBPV.Semantics Value Call Effect Fault Delay Suspension Context World Worker)
    (world : World) (context : Context)
    (enter : Atom → List Atom → Code (Value := Value) (Call := Call)
      (Effect := Effect) (Fault := Fault) (Delay := Delay) (Suspension := Suspension))
    (environment : Subst) (head : Atom) (operands : List Atom)

def sourceCode : Code (Value := Value) (Call := Call) (Effect := Effect) (Fault := Fault)
    (Delay := Delay) (Suspension := Suspension) :=
  (sourceEnter enter environment head operands).getD .failure

theorem kernel_entry_refines :
    ContextualCBPV.initial (Worker := Worker) world context (sourceCode enter environment head operands) =
      ContextualCBPV.initial (Worker := Worker) world context (targetEnter enter environment head operands) := by
  simp [sourceCode, entry_refines]

theorem kernel_slice_refines (allowance : Nat) :
    (ContextualCBPV.core sem world context).runSlice allowance
        (ContextualCBPV.initial (Worker := Worker) world context (sourceCode enter environment head operands)) =
      (ContextualCBPV.core sem world context).runSlice allowance
        (ContextualCBPV.initial (Worker := Worker) world context (targetEnter enter environment head operands)) := by
  rw [kernel_entry_refines]

end Kernel

namespace Controls

def readyCall : Subst := fun name => if name = "value" then some (.expression [.symbol "readln!"]) else none

theorem ready_value_stays_data :
    (project readyCall (.symbol "callee") [.var "value"]).arguments =
      [.expression [.symbol "readln!"]] := by
  simp [project_arguments, subst, readyCall]

theorem dropped_operand_changes_observation :
    (project readyCall (.symbol "callee") [.symbol "first", .symbol "second"]).arguments ≠
      [.symbol "first"] := by
  decide

theorem reversed_operands_change_observation :
    (project readyCall (.symbol "callee") [.symbol "first", .symbol "second"]).arguments ≠
      [.symbol "second", .symbol "first"] := by
  decide

theorem distinct_variables_remain_distinct :
    (project (fun _ => none) (.symbol "callee") [.var "first", .var "second"]).arguments ≠
      [.var "first", .var "first"] := by
  decide

end Controls

end Mettapedia.Machines.PlannedInvocationOperands
