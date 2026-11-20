import Mettapedia.Languages.MeTTa.PeTTa.AtomSchematicReads

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.AtomSchematicReads.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Subst subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax OneFrame SchematicRows
open AtomFreshNamespaces (X E)

private def integer (value : Int) : Atom := .grounded (.int value)
private def pair (first second : Atom) : Atom := .expression [.symbol "Pair", first, second]

private def closure : Closure (Terms Atom) PUnit.unit :=
  ⟨⟨PUnit.unit, [(.var "local", .var "local")], [.var "capture"],
      pair (.var "local") (.var "capture")⟩, [.var "caller"]⟩

private def caller : Subst := fun name => if name = "caller" then some (integer 9) else none

/-- Local variables vary freely; the captured caller variable remains nine. -/
theorem local_can_vary (value : Atom) :
    closure.ReadsAt X (b := PUnit.unit) caller (pair value (integer 9)) := by
  refine ⟨fun name => if name = "local" then some value else
      if name = "capture" then some (integer 9) else none, ?_, ?_, ?_⟩
  · intro equation inside
    obtain rfl := List.mem_singleton.mp inside
    rfl
  · exact List.Forall₂.cons rfl .nil
  · rfl

theorem separate_reads_can_choose_different_locals :
    closure.ReadsAt X (b := PUnit.unit) caller (pair (integer 7) (integer 9)) ∧
      closure.ReadsAt X (b := PUnit.unit) caller (pair (integer 8) (integer 9)) :=
  ⟨local_can_vary _, local_can_vary _⟩

theorem open_local_answer_is_permitted :
    closure.ReadsAt X (b := PUnit.unit) caller (pair (.var "unknown") (integer 9)) :=
  local_can_vary _

theorem capture_cannot_be_reinterpreted_as_an_independent_local :
    ¬ closure.ReadsAt X (b := PUnit.unit) caller (pair (integer 7) (integer 8)) := by
  rintro ⟨assignment, _, captures, output⟩
  have captured := (List.forall₂_cons.mp captures).1
  change subst assignment (.var "capture") = integer 9 at captured
  change pair (subst assignment (.var "local")) (subst assignment (.var "capture")) =
    pair (integer 7) (integer 8) at output
  rw [captured] at output
  simp [pair, integer] at output

private def ordinary : RuleSyntax.State (Terms Atom) Nat :=
  ⟨PUnit.unit, [(.var "caller", integer 9)], {0}, fun _ => .var "retained"⟩
private def rows : Finset Nat := {0}
private def closures (_ : Nat) := closure

theorem captured_read_has_constructed_freshness :
    (direct ordinary rows closures 0 1).Fresh X := direct_fresh ordinary rows closures 0 1

theorem malformed_capture_arity_prevents_admission :
    let malformed : Closure (Terms Atom) PUnit.unit := ⟨closure.schema, []⟩
    ¬ (direct ordinary rows (fun _ : Nat => malformed) 0 1).Admits X := by
  dsimp only
  intro admitted
  have formed := ((direct_admits_iff ordinary rows (fun _ : Nat => ⟨closure.schema, []⟩) 0 1).mp
    admitted).1
  change 1 = 0 at formed
  omega

theorem captured_read_has_a_real_two_event_execution :
    ∃ (run : (HeldReadGenericFirings.protocolMachine (E := E) (O := Nat) (R := Nat) X
        Set.univ).Run (HeldReadGenericSources.hosted ordinary rows closures)) (assignment : Subst),
      run.word.length = 2 ∧ X.Models (b := PUnit.unit) assignment run.last.knowledge ∧
      subst assignment (run.last.label 1) = pair (integer 7) (integer 9) ∧
      run.last.present = ordinary.present ∪ {1} ∧ run.last.rules = rows ∧ 2 ∉ run.last.present := by
  apply execution_of_reading ordinary rows closures 0 2 1 Set.univ (Set.mem_univ _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) caller
  · intro equation inside
    obtain rfl := List.mem_singleton.mp inside
    rfl
  · exact local_can_vary _

end Mettapedia.Languages.MeTTa.PeTTa.AtomSchematicReads.Controls
