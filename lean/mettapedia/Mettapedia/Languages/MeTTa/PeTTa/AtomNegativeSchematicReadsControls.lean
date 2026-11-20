import Mettapedia.Languages.MeTTa.PeTTa.AtomNegativeSchematicReads

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.AtomNegativeSchematicReads.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open RuleSyntax SchematicRows
open AtomNegativeFreshNamespaces (Frame Hom X)

private def integer (value : Int) : Atom := .grounded (.int value)
private def source : Frame := ⟨[(.var "x", integer 7)], by
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  change Atom.var "x" ≠ integer 7
  decide +kernel⟩

private def ordinary : RuleSyntax.State Terms Nat :=
  ⟨source, [], {0}, fun _ => .expression [.symbol "Saved", .var "x"]⟩
private def rows : Finset Nat := {0}
private def openData (_ : Nat) : RowData :=
  ⟨[], [.var "capture"], .expression [.symbol "Pair", .var "local", .var "capture"]⟩
private def arguments (_ : Nat) : List Atom := [.var "x"]

theorem open_row_and_caller_have_constructed_freshness :
    (direct ordinary rows openData arguments 0 2).Fresh X :=
  direct_fresh ordinary rows openData arguments 0 2

theorem both_actual_protocol_stages_have_constructed_freshness :
    (materialize ordinary rows openData arguments 0 1).Fresh X ∧
      (consume ordinary rows openData arguments 0 1 2).Fresh X :=
  stages_fresh ordinary rows openData arguments 0 1 2 Set.univ (by decide +kernel)

theorem reusing_one_opening_cannot_realize_independent_requests :
    ¬ ∃ (target : Frame) (assignment : Hom source target),
      X.act assignment (subst (AtomFreshNamespaces.opening (bound ordinary rows openData arguments) 0)
        (.var "local")) = integer 7 ∧
      X.act assignment (subst (AtomFreshNamespaces.opening (bound ordinary rows openData arguments) 0)
        (.var "local")) = integer 8 := by
  rintro ⟨target, assignment, first, second⟩
  exact (by decide +kernel : integer 7 ≠ integer 8) (first.symm.trans second)

theorem malformed_capture_arity_is_not_a_well_formed_closure :
    ¬ ((openData 0).close source []).WellFormed := by
  change ¬ (1 : Nat) = 0
  decide +kernel

private def constantData (_ : Nat) : RowData := ⟨[], [], integer 7⟩
private def noArguments (_ : Nat) : List Atom := []

private theorem constant_solvable :
    X.Solvable (a := source) ((direct ordinary rows constantData noArguments 0 2).information X) := by
  refine ⟨source, X.id source, ?_⟩
  unfold direct
  rw [HeldReadGenericFirings.direct_information (E := E) ordinary rows
    (closures ordinary constantData noArguments) 0 PUnit.unit
    (opening ordinary.frame (bound ordinary rows constantData noArguments) 0)
    (opening ordinary.frame (bound ordinary rows constantData noArguments) 1) X 2]
  intro equation member
  change equation ∈ [(integer 7, integer 7)] at member
  obtain rfl := List.mem_singleton.mp member
  rfl

theorem constant_read_has_two_real_events_and_retains_the_negative_frame :
    ∃ run : (HeldReadGenericFirings.protocolMachine (E := E) (O := Nat) (R := Nat) X Set.univ).Run
        (HeldReadGenericSources.hosted ordinary rows (closures ordinary constantData noArguments)),
      run.word.length = 2 ∧ run.last.present = {0, 2} ∧ run.last.rules = {0} ∧
        1 ∉ run.last.present ∧ run.last.frame = source := by
  obtain ⟨run, length, last, present, rulesAfter, privateAbsent⟩ :=
    execution_of_solvable ordinary rows constantData noArguments 0 1 2 Set.univ
      (Set.mem_univ _) rfl (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) constant_solvable
  refine ⟨run, length, ?_, rulesAfter, privateAbsent, ?_⟩
  · simpa [ordinary] using present
  · rw [last]
    rfl

end Mettapedia.Languages.MeTTa.PeTTa.AtomNegativeSchematicReads.Controls
