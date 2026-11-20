import Mettapedia.Languages.MeTTa.PeTTa.MachineNegativeHeadExecution

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MachineNegativeHeadExecution.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open RuleSyntax SchematicRows ListView
open Unifying (Idempotent idempotent_bindVar bindVar)
open UnifyingDisequality (solved solved_apply)
open AtomNegativeFreshNamespaces (Frame Hom X)
open AtomNegativeSchematicReads (Terms E closures)

private def integer (value : Int) : Atom := .grounded (.int value)
private def pair (first second : Atom) : Atom := .expression [.symbol "Pair", first, second]
private def frame : Frame := ⟨[(.var "caller", integer 7)], by
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  change Atom.var "caller" ≠ integer 7
  decide +kernel⟩
private def inputs : Subst := [("caller", integer 9)]
private theorem valid : Idempotent inputs := by
  change Idempotent (bindVar [] "caller" (integer 9))
  apply idempotent_bindVar idempotent_nil rfl
  · intro _ absent; cases absent
  · intro absent; cases absent

private def source : Atom := MachineClauseReads.row (.symbol "f") (integer 0)
  (MachineClauseReads.head (.expression [.var "caller"])) (pair (.var "caller") (.var "caller"))
private def query (value : Int) (body : Atom) : Atom :=
  MachineClauseReads.row (.symbol "f") (integer 0)
    (MachineClauseReads.head (.expression [integer value])) body
private def result := MachineHeadSelectionApart.probe frame inputs source (query 8 (.var "out"))
private def answer : Subst := match result with | .ok bound => bound | _ => []

theorem computed_probe_succeeds : result = .ok answer := by decide +kernel

theorem head_and_body_are_one_correlated_answer :
    subst (solved answer) (query 8 (.var "out")) = query 8 (pair (integer 8) (integer 8)) := by
  change atomAction.apply (solved answer) (query 8 (.var "out")) = _
  rw [solved_apply]
  decide +kernel

theorem caller_binding_is_not_the_local_binding :
    subst (solved answer) (.var "caller") = integer 9 := by
  change atomAction.apply (solved answer) (.var "caller") = _
  rw [solved_apply]
  decide +kernel

theorem independently_matching_body_fields_would_accept_too_much :
    MachineHeadSelectionApart.probe frame inputs source
      (query 8 (pair (integer 8) (integer 9))) = .clash := by decide +kernel

theorem caller_disequation_does_not_forbid_the_same_value_in_a_local_scope :
    MachineHeadSelection.accepted
      (MachineHeadSelectionApart.probe frame inputs source (query 7 (.var "out"))) = true := by
  decide +kernel

theorem an_incompatible_caller_frame_has_no_successful_probe :
    MachineHeadSelectionApart.probe frame [("caller", integer 7)] source
      (query 8 (.var "out")) = .clash := by decide +kernel

private def sources (_ : Nat) : Atom := source
private def present : Finset Nat := {0}
private def label (_ : Nat) : Atom := .expression [.symbol "Saved", .var "caller"]
private def rows : Finset Nat := {0}

private theorem snapshot_probe_succeeds :
    MachineNegativeHeadExecution.probe frame inputs present label source (query 8 (.var "out")) = .ok answer := by
  simp only [MachineNegativeHeadExecution.probe, AtomFreshNamespaces.sourceTerms,
    present, Finset.toList_singleton, List.map_singleton]
  exact computed_probe_succeeds

theorem actual_computed_clause_match_has_a_two_event_negative_frame_execution :
    ∃ (target : Frame) (run : (HeldReadGenericFirings.protocolMachine (E := E)
        (O := Nat) (R := Nat) X Set.univ).Run
        (HeldReadGenericSources.hosted (state frame inputs present label) rows
          (closures (state frame inputs present label) (data sources) (arguments (query 8 (.var "out")))))),
      run.word.length = 2 ∧ ∃ assignment : Hom run.last.frame target,
        X.Models assignment run.last.knowledge ∧
        X.act assignment (run.last.label 2) = query 8 (pair (integer 8) (integer 8)) ∧
        run.last.present = present ∪ {2} ∧ run.last.rules = rows ∧ 1 ∉ run.last.present := by
  have executed := computed_execution frame inputs answer present label rows sources 0 1 2
    (query 8 (.var "out")) Set.univ (Set.mem_univ _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) valid snapshot_probe_succeeds
  simpa only [head_and_body_are_one_correlated_answer] using executed

private def emptyFrame : Frame := ⟨[], by intro _ absent; cases absent⟩
private def oldName : Atom := .var (LibTransformStep.tag 0 "x")
private def retainedLabel (_ : Nat) : Atom := .expression [.symbol "Saved", oldName]
private def safeAnswer : Subst :=
  match MachineHeadSelectionApart.probe emptyFrame [] (.var "x") (integer 7) [retainedLabel 0] with
  | .ok answer => answer
  | _ => []

theorem actual_state_adapter_protects_names_outside_the_query :
    MachineNegativeHeadExecution.probe emptyFrame [] present retainedLabel (.var "x") (integer 7) =
        .ok safeAnswer ∧ Unifying.resolve safeAnswer oldName = oldName := by
  constructor
  · simp only [MachineNegativeHeadExecution.probe, AtomFreshNamespaces.sourceTerms,
      UnifyingConstraintPresentation.presentation, List.map_nil, List.nil_append,
      present, Finset.toList_singleton, List.map_singleton]
    decide +kernel
  · decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.MachineNegativeHeadExecution.Controls
