import Mettapedia.Languages.MeTTa.PeTTa.MachineClauseActivation

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MachineClauseActivation.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation (presentation)
open RuleSyntax OneFrame SchematicRows
open ListView Unifying UnifyingDisequality
open AtomFreshNamespaces (X E)

private def integer (value : Int) : Atom := .grounded (.int value)
private def pair (first second : Atom) : Atom := .expression [.symbol "Pair", first, second]
private def inputs : Subst := [("caller", integer 9)]
private def source : Atom := MachineClauseReads.row (.symbol "f") (integer 0)
  (MachineClauseReads.head (.expression [.var "x"])) (pair (.var "x") (.var "capture"))
private def query : Atom := MachineClauseReads.row (.symbol "f") (integer 0)
  (MachineClauseReads.head (.expression [integer 7])) (.var "out")
private def parameters : List Atom := [.var "capture"]
private def arguments : List Atom := [.var "caller"]
private def scope : Nat := freshScope inputs query arguments
private def result : Unified := unifyBinding inputs
  (GSLTBindingPatterns.quoted (LibTransformStep.rename scope (packet source parameters)))
  (packet query arguments)
private def answer : Subst := match result with | .ok bound => bound | _ => []

private theorem inputs_valid : Idempotent inputs := by
  change Idempotent (bindVar [] "caller" (integer 9))
  apply idempotent_bindVar idempotent_nil rfl
  · intro _ absent
    cases absent
  · intro absent
    cases absent

theorem computed_packet_succeeds : result = .ok answer := by decide +kernel

theorem computed_packet_keeps_body_and_capture_correlated :
    subst (solved answer) (.var "out") = pair (integer 7) (integer 9) := by
  change atomAction.apply (solved answer) (.var "out") = _
  rw [solved_apply]
  decide +kernel

theorem inconsistent_capture_is_not_an_independent_success :
    unifyBinding inputs
      (GSLTBindingPatterns.quoted (LibTransformStep.rename scope (packet source [.var "x"])))
      (packet query arguments) = .clash := by decide +kernel

theorem capture_arity_is_checked_by_the_same_match :
    unifyBinding inputs
      (GSLTBindingPatterns.quoted (LibTransformStep.rename scope
        (packet source [.var "capture", .var "other"])))
      (packet query arguments) = .clash := by decide +kernel

theorem existing_encoded_query_name_advances_the_namespace :
    freshScope [] (.var (LibTransformStep.tag 25 "λ")) [] = 26 := by decide +kernel

theorem actual_computed_answer_is_a_closure_reading :
    (closure PUnit.unit source parameters arguments).ReadsAt X (b := PUnit.unit) (solved answer)
      (subst (solved answer) query) := computed_reading PUnit.unit inputs_valid computed_packet_succeeds

private def ordinary : RuleSyntax.State (Terms Atom) Nat :=
  ⟨PUnit.unit, presentation inputs, {0}, fun _ => .expression [.symbol "Saved", .var "later"]⟩
private def rows : Finset Nat := {0}
private def closures (_ : Nat) := closure PUnit.unit source parameters arguments

theorem actual_computed_packet_has_a_two_event_execution :
    ∃ (run : (HeldReadGenericFirings.protocolMachine (E := E) (O := Nat) (R := Nat) X Set.univ).Run
        (HeldReadGenericSources.hosted ordinary rows closures)) (assignment : StepSubstitution),
      run.word.length = 2 ∧ X.Models (b := PUnit.unit) assignment run.last.knowledge ∧
      subst assignment (run.last.label 1) = subst (solved answer) query ∧
      run.last.present = ordinary.present ∪ {1} ∧ run.last.rules = rows ∧ 2 ∉ run.last.present :=
  computed_execution ordinary rows closures 0 2 1 Set.univ (Set.mem_univ _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    rfl rfl inputs_valid computed_packet_succeeds

end Mettapedia.Languages.MeTTa.PeTTa.MachineClauseActivation.Controls
