import Mettapedia.Machines.ExecutionControl
import Mettapedia.Languages.MeTTa.PeTTa.ValueOccurrences

/-!
# Written operands and held dispatch values

A dispatch source either supplies a ready value or an application with a ready
head and written operands. The latter operands retain their own occurrence
plans through substitution. The target reads a program-owned plan beside the
substituted image; it does not recover operand demand from that image.

The head is already a value in this boundary. Computing a dynamic head, native
ownership and source charging remain obligations of the surrounding machine.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.DispatchOperands

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Subst subst)
open Mettapedia.Languages.MeTTa.PeTTa

inductive Source where
  | held (value : Atom)
  | written (head : Atom) (operands : List Atom)

inductive Image where
  | ready (value : Atom)
  | application (head : Atom) (operands : List Atom)

structure Plan where
  argumentPlans : Option (List ValueOccurrences.Plan)

def compile : Source → Plan
  | .held _ => ⟨none⟩
  | .written _ operands => ⟨some (ValueOccurrences.planOf.planOfList operands)⟩

def image (σ : Subst) : Source → Image
  | .held value => .ready value
  | .written head operands => .application head (subst.substList σ operands)

/-- Source preparation evaluates written operands, preserving each answer
occurrence. Held values have no operand computations to perform. -/
def referenceRequests (program : ValueOccurrences.Program) (σ : Subst) : Source → List Atom
  | .held value => match value with
      | .expression (_ :: _) => [value]
      | _ => []
  | .written head operands =>
      (ValueOccurrences.choices (ValueOccurrences.evalIn.evalList program σ operands)).map
        (fun values => .expression (head :: values))

/-- The target follows the supplied plans. A mismatched image is refused. -/
def targetRequests (program : ValueOccurrences.Program) (plan : Plan) (payload : Image) :
    Option (List Atom) :=
  match plan.argumentPlans, payload with
  | none, .ready value => some (match value with
      | .expression (_ :: _) => [value]
      | _ => [])
  | some plans, .application head operands =>
      some ((ValueOccurrences.choices (ValueOccurrences.evalPlanned.evalPlannedList program plans operands)).map
        (fun values => .expression (head :: values)))
  | _, _ => none

theorem operand_plans_refine (program : ValueOccurrences.Program) (σ : Subst)
    (operands : List Atom) :
    ValueOccurrences.evalPlanned.evalPlannedList program (ValueOccurrences.planOf.planOfList operands)
      (subst.substList σ operands) = ValueOccurrences.evalIn.evalList program σ operands := by
  induction operands with
  | nil => rfl
  | cons first rest ih =>
      simp only [ValueOccurrences.planOf.planOfList, subst.substList,
        ValueOccurrences.evalPlanned.evalPlannedList, ValueOccurrences.evalIn.evalList]
      rw [ValueOccurrences.evalPlanned_planOf_subst, ih]

theorem compile_refines (program : ValueOccurrences.Program) (σ : Subst) (source : Source) :
    targetRequests program (compile source) (image σ source) =
      some (referenceRequests program σ source) := by
  cases source with
  | held value => rfl
  | written head operands =>
      simp only [compile, image, targetRequests, referenceRequests]
      rw [operand_plans_refine]

/-- A completed dispatch result is delivered directly, including an
expression-shaped result; its children are not evaluated again. -/
def dispatch (program : ValueOccurrences.Program) : Atom → List Atom
  | .expression [] => []
  | .expression items => ValueOccurrences.finish program items
  | _ => []

def reference (program : ValueOccurrences.Program) (σ : Subst) (source : Source) : List Atom :=
  (referenceRequests program σ source).flatMap (dispatch program)

def target (program : ValueOccurrences.Program) (plan : Plan) (payload : Image) :
    Option (List Atom) :=
  (targetRequests program plan payload).map (fun requests =>
    requests.flatMap (dispatch program))

theorem answers_refine (program : ValueOccurrences.Program) (σ : Subst) (source : Source) :
    target program (compile source) (image σ source) =
      some (reference program σ source) := by
  simp only [target, compile_refines, Option.map_some, reference]

/-- Prefix observers retain the ordered answer occurrences, not just a set. -/
theorem answer_prefix_refines (program : ValueOccurrences.Program) (σ : Subst)
    (source : Source) (count : Nat) :
    (target program (compile source) (image σ source)).map (List.take count) =
      some ((reference program σ source).take count) := by
  rw [answers_refine]
  rfl

theorem held_refuses_written_image (program : ValueOccurrences.Program) (value head : Atom)
    (operands : List Atom) :
    targetRequests program (compile (.held value)) (.application head operands) = none := rfl

theorem written_refuses_ready_image (program : ValueOccurrences.Program) (head value : Atom)
    (operands : List Atom) :
    targetRequests program (compile (.written head operands)) (.ready value) = none := rfl

/-- The surrounding contextual machine receives invocation, not force. -/
theorem ready_continuation (wrapper value : Atom) :
    (ExecutionControl.Forcing.readReady .invoke #[wrapper, value] :
      Option (ContextualCBPV.Code Atom Atom Unit Unit Unit Unit)) =
      some (.invoke value) := rfl

private def separating : ValueOccurrences.Program where
  isCall := fun items => match items with
    | .symbol "keep" :: _ | .symbol "work" :: _ => true
    | _ => false
  answers := fun items => match items with
    | [.symbol "keep", value] => [value]
    | [.symbol "work"] => [.symbol "executed", .symbol "executed"]
    | _ => []

private def work : Atom := .expression [.symbol "work"]
private def held : Atom := .expression [.symbol "keep", work]

theorem held_result_stays_data :
    reference separating (fun _ => none) (.held held) = [work] := by decide

theorem forcing_held_arguments_changes_answers :
    ValueOccurrences.evalCode separating held ≠
      reference separating (fun _ => none) (.held held) := by decide

theorem written_operands_keep_duplicates :
    reference separating (fun _ => none) (.written (.symbol "keep") [work]) =
      [.symbol "executed", .symbol "executed"] := by decide

theorem nonapplication_dispatch_has_no_answer :
    referenceRequests separating (fun _ => none) (.held (.symbol "literal")) = [] ∧
      reference separating (fun _ => none) (.held (.symbol "literal")) = [] := by decide

theorem nonapplication_force_is_a_value :
    ValueOccurrences.evalCode separating (.symbol "literal") = [.symbol "literal"] := by decide

theorem empty_application_dispatch_has_no_answer :
    referenceRequests separating (fun _ => none) (.held (.expression [])) = [] ∧
      reference separating (fun _ => none) (.held (.expression [])) = [] := by decide

end Mettapedia.Machines.DispatchOperands

#print axioms Mettapedia.Machines.DispatchOperands.operand_plans_refine
#print axioms Mettapedia.Machines.DispatchOperands.compile_refines
#print axioms Mettapedia.Machines.DispatchOperands.answers_refine
#print axioms Mettapedia.Machines.DispatchOperands.answer_prefix_refines
#print axioms Mettapedia.Machines.DispatchOperands.held_refuses_written_image
#print axioms Mettapedia.Machines.DispatchOperands.written_refuses_ready_image
#print axioms Mettapedia.Machines.DispatchOperands.ready_continuation
#print axioms Mettapedia.Machines.DispatchOperands.held_result_stays_data
#print axioms Mettapedia.Machines.DispatchOperands.forcing_held_arguments_changes_answers
#print axioms Mettapedia.Machines.DispatchOperands.written_operands_keep_duplicates
#print axioms Mettapedia.Machines.DispatchOperands.nonapplication_dispatch_has_no_answer
#print axioms Mettapedia.Machines.DispatchOperands.nonapplication_force_is_a_value
#print axioms Mettapedia.Machines.DispatchOperands.empty_application_dispatch_has_no_answer
