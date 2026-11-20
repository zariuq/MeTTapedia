import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStreamingRegionControls

/-! The actual controller carries region proofs across partial execution and
resumption. The nested control retains its outer collection and rejects the
second answer before it can reach that bank. -/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStreamingRegionControls

def sample (label : String) (fuel : Nat) : IO Unit := do
  let reached := Streaming.Regions.advanceLinked program fuel ⟨nestedFirst,nested_first_is_wellFormed⟩
  IO.println s!"{label}: pending={reached.val.agenda.length} markers={(Streaming.Regions.markers reached.val.agenda).length} answers={reached.val.answers.length} uses={reached.val.world.uses}"

def main : IO Unit := do
  sample "entry" 0
  sample "cut" 1
  sample "bank" 2
  sample "close" 3
  sample "done" 4
  let one := Streaming.Regions.advanceLinked program 1 ⟨nestedFirst,nested_first_is_wellFormed⟩
  let resumed := Streaming.Regions.advanceLinked program 3 one
  IO.println s!"resumed: {Atom.toString (.expression (Streaming.values resumed.val))}"
  let outside := Streaming.Regions.advanceLinked program 2
    ⟨outsideHandler,returned_caller_can_be_outside_an_old_handler⟩
  IO.println s!"returned: {Atom.toString (.expression (Streaming.values outside.val))}"
  let expression := Atom.expression [.symbol "collapse",
    .expression [.symbol "let",.var "x",.expression [.symbol "superpose",.expression [.symbol "a",.symbol "b"]],
      .expression [.symbol "collapse",.expression [.symbol "superpose",.expression [.var "x",.var "x"]]]]]
  let nested := Streaming.Regions.advanceLinked program 200
    (Streaming.Regions.enterLinked {state := Effects.empty} expression)
  match Streaming.observe nested.val with
  | .complete reached => IO.println s!"nested: {Atom.toString (.expression (Streaming.values reached))}"
  | .suspended _ => throw (IO.userError "nested collection suspended")
  | .fault reason _ => throw (IO.userError s!"nested collection fault: {reprStr reason}")
