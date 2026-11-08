import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshRangeAlias

/-!
# Alias-explicit representatives at logical equation publication

Bare variable assignments are exposed as equality constraints by the existing
`aliasConstraints` operation. Its complete theory and support agreement earns
`Frame.represent`, which keeps the exact annotated environment and every read.
Equation frontiers already publish a logical conjunction rather than a chosen
raw merge layout, so this representation is constructed at that source
boundary without changing expected-type syntax or equation occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEAliasExplicitFrames

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Type.Presentation Spec.Type.Presentation.BindingTheory
open Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation
open Spec.Match.ModelTheory Spec.Eval Spec.Eval.Completed Spec.Eval.Steps

theorem agreement (bindings : Bindings) : BindingSourceAgreement bindings (aliasConstraints bindings) :=
  ⟨fun model => (aliasConstraints_models bindings model).symm,
    fun name => (aliasConstraints_support bindings name).symm⟩

def explicitFrame (frame : Frame) : Frame :=
  frame.represent (aliasConstraints frame.bindings) (agreement frame.bindings)

theorem explicit_bindings (frame : Frame) :
    (explicitFrame frame).bindings = aliasConstraints frame.bindings := rfl

theorem explicit_shape (frame : Frame) : AssignmentsNonVariable (explicitFrame frame).bindings :=
  aliasConstraints_nonvariable frame.bindings

theorem explicit_environment (frame : Frame) : (explicitFrame frame).environment = frame.environment := rfl

theorem explicit_read (frame : Frame) (policy : Policy) (value : Entry.Value) :
    (explicitFrame frame).read policy value = frame.read policy value := rfl

theorem logical_output {left right output : Bindings} (merged : LogicalMergeRel left right output) :
    LogicalMergeRel left right (aliasConstraints output) := by
  obtain ⟨model, satisfied⟩ := merged.2
  exact ⟨(agreement output).symm.trans merged.1,
    model, (agreement output).solutions model |>.mp satisfied⟩

def explicitWork (work : EquationWork) : EquationWork :=
  { work with bindings := aliasConstraints work.bindings }

theorem row_explicit {live : List Atom} {query : Atom} {incoming : Bindings}
    {position : Nat} {row : Atom} {works : List EquationWork}
    (selected : EquationRowResultsRel live query incoming position row works) :
    EquationRowResultsRel live query incoming position row (works.map explicitWork) := by
  cases selected with
  | irrelevant row absent => exact .irrelevant position row absent
  | miss left right pattern body fresh refused => exact .miss position left right pattern body fresh refused
  | hit left right pattern body matched output fresh matching merged =>
      exact .hit position left right pattern body matched (aliasConstraints output) fresh matching (logical_output merged)

theorem frontier_explicit {space : Space} {live : List Atom} {query : Atom} {incoming : Bindings}
    {works : List EquationWork} (frontier : EquationFrontierRel space live query incoming works) :
    EquationFrontierRel space live query incoming (works.map explicitWork) := by
  cases frontier with
  | @completed blocks paired =>
      have mapped : List.Forall₂ (fun row block => EquationRowResultsRel live query incoming row.2 row.1 block)
          space.atoms.zipIdx (blocks.map (List.map explicitWork)) := by
        generalize space.atoms.zipIdx = rows at paired ⊢
        induction paired with
        | nil => exact .nil
        | cons row rest ih => exact .cons (row_explicit row) ih
      simpa only [List.map_flatten] using EquationFrontierRel.completed mapped

theorem explicit_work_frame (work : EquationWork) (frame : Frame) (bindings : frame.bindings = work.bindings) :
    (explicitFrame frame).bindings = (explicitWork work).bindings := by
  simp [explicitFrame, explicitWork, Frame.represent, bindings]

/-- The actual contextual unifier is retained verbatim. Only its chosen
source constraint presentation changes at logical output publication. -/
theorem explicit_unifier (policy : Policy) (before after : Frame) (left right : Entry.Value)
    (unified : Entry.Value.UnifyRel policy.rebuilding before.environment left right after.environment) :
    Entry.Value.UnifyRel policy.rebuilding before.environment left right (explicitFrame after).environment := unified

namespace Controls

theorem alias_record_changes_without_changing_reads (policy : Policy) (value : Entry.Value) :
    (explicitFrame Spec.Eval.Completed.Controls.argumentAliasFrame).bindings.assignments = [] ∧
    (explicitFrame Spec.Eval.Completed.Controls.argumentAliasFrame).bindings.equalities = [("x", "y")] ∧
    (explicitFrame Spec.Eval.Completed.Controls.argumentAliasFrame).read policy value =
      Spec.Eval.Completed.Controls.argumentAliasFrame.read policy value := by
  exact ⟨rfl, rfl, explicit_read _ policy value⟩

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEAliasExplicitFrames
