import Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-!
# Operand admission at the completed source boundary

The role interface changes only applicability. Its historical query-based
instance gives the same ordered batches and selected frames as the original
source relation, including repeated query occurrences and diagnostics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type

/-- A successful metatype check on the authored formal does not query the
subject's inferred types. Other formals use the complete inferred service. -/
inductive ArgumentKindCut : Atom → Atom → Prop where
  | atom (kind : Atom) : ArgumentKindCut Atom.atomType kind
  | symbol : ArgumentKindCut Atom.symbolType Atom.symbolType
  | variable : ArgumentKindCut Atom.variableType Atom.variableType
  | grounded : ArgumentKindCut Atom.groundedType Atom.groundedType
  | expression : ArgumentKindCut Atom.expressionType Atom.expressionType

inductive KindArgumentAdmissionRel (space : Space) (inferred : TypeLookupRel) (policy : Policy)
    (expression subject formal : Atom) (position : Nat) : Frame → List Frame → List Atom → Prop where
  | kind {before kind} : MetaTypeRel subject kind → ArgumentKindCut formal kind →
      KindArgumentAdmissionRel space inferred policy expression subject formal position before [before] []
  | inferred {before frames errors} :
      (∀ kind, MetaTypeRel subject kind → ¬ArgumentKindCut formal kind) →
      ArgumentChecksRel space inferred policy expression subject formal position [before] frames errors →
      KindArgumentAdmissionRel space inferred policy expression subject formal position before frames errors

def kindArgumentService : ArgumentService := .role KindArgumentAdmissionRel

theorem KindArgumentAdmissionRel.kind_exact
    {space inferred policy expression subject formal position before frames errors kind}
    (kindOf : MetaTypeRel subject kind) (cut : ArgumentKindCut formal kind)
    (admitted : KindArgumentAdmissionRel space inferred policy expression subject formal position before frames errors) :
    frames = [before] ∧ errors = [] := by
  cases admitted with
  | kind => exact ⟨rfl, rfl⟩
  | inferred absent _ => exact (absent kind kindOf cut).elim

theorem AdmissionFramesRel.single
    {admit space lookup policy expression subject formal position before frames errors}
    (admitted : admit space lookup policy expression subject formal position before frames errors) :
    AdmissionFramesRel admit space lookup policy expression subject formal position [before] frames errors := by
  simpa only [List.append_nil] using AdmissionFramesRel.cons admitted AdmissionFramesRel.nil

theorem KindArgumentAdmissionRel.held
    (space : Space) (inferred : TypeLookupRel) (policy : Policy) (expression subject : Atom)
    (position : Nat) (before : Frame) :
    KindArgumentAdmissionRel space inferred policy expression subject Atom.atomType position before [before] [] := by
  cases subject with
  | symbol name => exact .kind (.symbol name) (.atom _)
  | var name => exact .kind (.variable name) (.atom _)
  | grounded value => exact .kind (.grounded value) (.atom _)
  | expression children => exact .kind (.expression children) (.atom _)

/-- Arbitrary held operands retain exactly one caller occurrence without
assuming even one answer from the inferred-type service. -/
theorem AdmissionArgumentsRel.all_held
    (space : Space) (inferred : TypeLookupRel) (policy : Policy) (expression : Atom)
    (subjects : List Atom) (position : Nat) (before : Frame) :
    AdmissionArgumentsRel KindArgumentAdmissionRel space inferred policy expression position
      subjects (List.replicate subjects.length Atom.atomType) [before] [before] [] := by
  induction subjects generalizing position with
  | nil => exact .nil
  | cons subject subjects ih =>
      exact .cons (AdmissionFramesRel.single
        (KindArgumentAdmissionRel.held space inferred policy expression subject position before)) (ih (position + 1))

/-- The no-query case is not an alternative spelling of a successful
global type lookup: the historical checker cannot consume this operand. -/
theorem held_without_inference (space : Space) (policy : Policy)
    (expression subject : Atom) (position : Nat) (before : Frame) :
    KindArgumentAdmissionRel space (fun _ _ _ _ => False) policy expression subject Atom.atomType position before [before] [] ∧
      ¬∃ outputs errors, ArgumentChecksRel space (fun _ _ _ _ => False) policy
        expression subject Atom.atomType position [before] outputs errors := by
  refine ⟨KindArgumentAdmissionRel.held _ _ _ _ _ _ _, ?_⟩
  rintro ⟨outputs, errors, admitted⟩
  cases admitted with
  | cons impossible _ _ => exact impossible

def queriedArgument : ArgumentAdmission :=
  fun space lookup policy expression argument expected position before outputs errors =>
    ArgumentChecksRel space lookup policy expression argument expected position [before] outputs errors

theorem ArgumentService.single_nonfunction (service : ArgumentService)
    {space lookup policy live scope expression operator expected before candidate}
    (queried : lookup (invocationTypeScope scope live expression expected before.bindings) space
      before.bindings operator Atom.undefinedType [candidate])
    (nonFunction : ¬∃ domains returned, FunctionTypeRel candidate domains returned) :
    service.selection space lookup policy live scope expression operator expected before (.exhausted [] true) := by
  cases service with
  | historical => exact ⟨[candidate], queried, .nonFunction nonFunction .nil⟩
  | role _ => exact ⟨[candidate], queried, .nonFunction nonFunction .nil⟩

theorem ArgumentChecksRel.append
    {space lookup policy expression argument expected position before middle first second errors later}
    (left : ArgumentChecksRel space lookup policy expression argument expected position before first errors)
    (right : ArgumentChecksRel space lookup policy expression argument expected position middle second later) :
    ArgumentChecksRel space lookup policy expression argument expected position
      (before ++ middle) (first ++ second) (errors ++ later) := by
  induction left with
  | nil => exact right
  | cons queried checks rest ih =>
      simpa only [List.cons_append, List.append_assoc] using
        ArgumentChecksRel.cons queried checks ih

theorem AdmissionFramesRel.queried_iff
    {space lookup policy expression argument expected position before after errors} :
    AdmissionFramesRel queriedArgument space lookup policy expression argument expected position before after errors ↔
      ArgumentChecksRel space lookup policy expression argument expected position before after errors := by
  constructor
  · intro source
    induction source with
    | nil => exact .nil
    | cons first _ ih => exact first.append ih
  · intro source
    induction source with
    | nil => exact .nil
    | @cons frame rest actuals checks outputs errors queried paired remaining ih =>
        have one : queriedArgument space lookup policy expression argument expected position frame
            (checkedFrames checks) ((checkedFailures checks).map
              (fun actual => mkError expression (.badArgType position expected actual))) := by
          simpa only [queriedArgument, List.append_nil] using ArgumentChecksRel.cons queried paired ArgumentChecksRel.nil
        exact .cons one ih

theorem AdmissionArgumentsRel.queried_iff
    {space lookup policy expression position arguments expecteds before after errors} :
    AdmissionArgumentsRel queriedArgument space lookup policy expression position arguments expecteds before after errors ↔
      ApplicabilityArgumentsRel space lookup policy expression position arguments expecteds before after errors := by
  constructor
  · intro source
    induction source with
    | nil => exact .nil
    | cons first _ ih => exact .cons (AdmissionFramesRel.queried_iff.mp first) ih
  · intro source
    induction source with
    | nil => exact .nil
    | cons first _ ih => exact .cons (AdmissionFramesRel.queried_iff.mpr first) ih

theorem AdmissionApplicationRel.queried_iff
    {space lookup policy expression expected selected before after errors} :
    AdmissionApplicationRel queriedArgument space lookup policy expression expected selected before after errors ↔
      ApplicationChecksRel space lookup policy expression expected selected before after errors := by
  constructor
  · intro source
    cases source with
    | wrongArity shaped different => exact .wrongArity shaped different
    | checked shaped arguments returned =>
        exact .checked shaped (AdmissionArgumentsRel.queried_iff.mp arguments) returned
  · intro source
    cases source with
    | wrongArity shaped different => exact .wrongArity shaped different
    | checked shaped arguments returned =>
        exact .checked shaped (AdmissionArgumentsRel.queried_iff.mpr arguments) returned

theorem AdmissionScanRel.queried_iff
    {space lookup policy expression expected before candidates outcome} :
    AdmissionScanRel queriedArgument space lookup policy expression expected before candidates outcome ↔
      InvocationScanRel space lookup policy expression expected before candidates outcome := by
  constructor
  · intro source
    induction source with
    | nil => exact .nil
    | nonFunction absent _ ih => exact .nonFunction absent ih
    | selected checked present => exact .selected (AdmissionApplicationRel.queried_iff.mp checked) present
    | rejected checked _ ih => exact .rejected (AdmissionApplicationRel.queried_iff.mp checked) ih
  · intro source
    induction source with
    | nil => exact .nil
    | nonFunction absent _ ih => exact .nonFunction absent ih
    | selected checked present => exact .selected (AdmissionApplicationRel.queried_iff.mpr checked) present
    | rejected checked _ ih => exact .rejected (AdmissionApplicationRel.queried_iff.mpr checked) ih

theorem queried_role_selection_iff
    {space lookup policy live scope expression operator expected before outcome} :
    (ArgumentService.role queriedArgument).selection space lookup policy live scope
      expression operator expected before outcome ↔
      InvocationSelectionRel space lookup policy live scope expression operator expected before outcome := by
  constructor
  · rintro ⟨candidates, queried, scanned⟩
    exact ⟨candidates, queried, AdmissionScanRel.queried_iff.mp scanned⟩
  · rintro ⟨candidates, queried, scanned⟩
    exact ⟨candidates, queried, AdmissionScanRel.queried_iff.mpr scanned⟩

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
