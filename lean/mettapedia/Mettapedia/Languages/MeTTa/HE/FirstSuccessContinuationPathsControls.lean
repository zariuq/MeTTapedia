import Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution

/-! The first-success append frame retains both occurrences of an identical
reply and resumes the same caller after a one-step pause. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessContinuationPathsControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks FirstSuccessRecursiveExecution
open FirstSuccessSourceExecution
open Mettapedia.GSLT.Distinction.ProductiveBlocks

private def original : Atom := .expression [.symbol "pending", .symbol "command"]
private def input : ResultPair := (Atom.notReducible, Bindings.empty)
private def output : ResultPair := (original, Bindings.empty)
private def task (rows : ResultSet) : Task :=
  .returns original Atom.atomType 0 rows []
private def machine := Checked.machine HE.GroundedDispatch.none

theorem duplicate_rows_preserved :
    Covered.Realizes Space.empty (task [input, input]) [output, output] := by
  have child := Covered.returned_notReducible_realizes
    Space.empty original Atom.atomType Bindings.empty 0 []
  exact Covered.returns_realizes Space.empty original Atom.atomType 0 []
    (requests := [input, input]) (outputs := [[output], [output]])
    (.cons child (.cons child .nil))

example :
    machine.run 1 ⟨Space.empty, .work (task [input, input]), [.prepend [output]], [output]⟩ =
      ([], .exhausted ⟨Space.empty,
        .work (.returned original input.1 Atom.atomType input.2 0 []),
        [.append (task [input]), .prepend [output]], [output]⟩) := rfl

theorem duplicate_row_cannot_be_discarded (budget : Nat) (finished : Configuration) :
    machine.run budget ⟨Space.empty, .work (task [input, input]), [], []⟩ ≠
      ([output], .finished finished) := by
  intro collapsed
  obtain ⟨_, complete⟩ := Covered.realizes_completed duplicate_rows_preserved []
  have same := (Machine.finished_run_eq collapsed complete).1
  have lengths := congrArg List.length same
  cases lengths

end Mettapedia.Languages.MeTTa.HE.FirstSuccessContinuationPathsControls
