import Mettapedia.Languages.MeTTa.PeTTa.AtomNegativeSchematicReading

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.AtomNegativeSchematicReading.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open RuleSyntax SchematicRows
open AtomNegativeFreshNamespaces (Frame Hom X)
open AtomNegativeSchematicReads (Terms E closures bound opening direct)

private def integer (value : Int) : Atom := .grounded (.int value)
private def pair (first second : Atom) : Atom := .expression [.symbol "Pair", first, second]
private def source : Frame := ⟨[(.var "x", integer 7)], by
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  change Atom.var "x" ≠ integer 7
  decide +kernel⟩
private def callerAssignment : Subst := fun name => if name = "x" then some (integer 9) else none
private theorem caller_separates : Disequality.Separates atomAction callerAssignment source.1 := by
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  change integer 9 ≠ integer 7
  decide +kernel
private def target : Frame := Disequality.image callerAssignment source.1 caller_separates
private def caller : Hom source target := Disequality.toImage source callerAssignment caller_separates
private def ordinary : RuleSyntax.State Terms Nat :=
  ⟨source, [(.var "x", integer 9)], {0}, fun _ => .expression [.symbol "Saved", .var "x"]⟩
private def rows : Finset Nat := {0}
private def data (_ : Nat) : AtomNegativeSchematicReads.RowData :=
  ⟨[], [.var "capture"], pair (.var "x") (.var "capture")⟩
private def arguments (_ : Nat) : List Atom := [.var "x"]
private def localAssignment : Subst := fun name =>
  if name = "x" then some (integer 7)
  else if name = "capture" then some (integer 9) else none
private def localPoint : Hom AtomNegativeSchematicReads.emptyFrame target :=
  ⟨localAssignment, by intro _ _ _ absent; cases absent⟩

private theorem known : X.Models caller ordinary.knowledge := by
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  rfl

theorem independent_reading_keeps_caller_nine_and_local_seven :
    (closures ordinary data arguments 0).ReadsAt X caller (pair (integer 7) (integer 9)) := by
  refine ⟨localPoint, ?_, ?_, ?_⟩
  · intro _ absent
    cases absent
  · exact .cons rfl .nil
  · rfl

theorem direct_matching_model_is_constructed_from_the_reading :
    ∃ assignment : Hom source target,
      X.Models assignment ((direct ordinary rows data arguments 0 2).information X) ∧
      X.act assignment (.var "x") = integer 9 ∧
      X.act assignment (X.act (opening ordinary.frame (bound ordinary rows data arguments) 0)
        (data 0).value) = pair (integer 7) (integer 9) := by
  obtain ⟨assignment, solved, kept, result⟩ := direct_model_of_reading ordinary rows data arguments
    0 2 caller (by decide +kernel) known _ independent_reading_keeps_caller_nine_and_local_seven
  refine ⟨assignment, solved, ?_, result⟩
  apply kept
  left
  change Atom.var "x" ∈ [Atom.var "x"]
  exact List.mem_singleton_self _

theorem actual_two_event_run_returns_the_independently_read_value :
    ∃ run : (HeldReadGenericFirings.protocolMachine (E := E) (O := Nat) (R := Nat) X Set.univ).Run
        (HeldReadGenericSources.hosted ordinary rows (closures ordinary data arguments)),
      run.word.length = 2 ∧ ∃ assignment : Hom run.last.frame target,
        X.Models assignment run.last.knowledge ∧
        X.act assignment (run.last.label 2) = pair (integer 7) (integer 9) ∧
        run.last.present = ordinary.present ∪ {2} ∧ run.last.rules = rows ∧
          1 ∉ run.last.present :=
  execution_of_reading ordinary rows data arguments 0 1 2 Set.univ (Set.mem_univ _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    caller known _ independent_reading_keeps_caller_nine_and_local_seven

private def inconsistentData : AtomNegativeSchematicReads.RowData :=
  ⟨[(.var "capture", integer 7)], [.var "capture"], .var "capture"⟩

theorem incompatible_local_knowledge_and_capture_have_no_reading (value : Atom) :
    ¬ (inconsistentData.close source [.var "x"]).ReadsAt X caller value := by
  rintro ⟨point, localKnown, captures, _⟩
  have localValue : X.act point (.var "capture") = integer 7 :=
    localKnown (.var "capture", integer 7) (List.mem_singleton_self _)
  have shared : X.act point (.var "capture") = integer 9 := by
    cases captures with
    | cons matched _ => exact matched
  exact (by decide +kernel : integer 7 ≠ integer 9) (localValue.symm.trans shared)

end Mettapedia.Languages.MeTTa.PeTTa.AtomNegativeSchematicReading.Controls
